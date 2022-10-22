package lark.meta.core.obc

import lark.meta.base.{names, pretty}
import lark.meta.base.names.given
import lark.meta.base.collection.MultiMap

import lark.meta.core.Sort
import lark.meta.core.term.Exp
import lark.meta.core.term

import lark.meta.core.obc.Obc.{Statement, Method, Class, Program, Storage}

import scala.collection.immutable.SortedMap

/** Typechecking for Obc, the imperative object language */
object Check:

  case class Env(
    values: term.Check.Env,
    classes: names.immutable.RefMap[Class],
    self: Class
  )

  /** Options for typechecking programs.
   *
   * @param callsReturnLocals
   *  If true, the storage struct returned by method calls will also include
   *  local variables, including the method call's nested method calls. This
   *  option is useful when invariants need to refer to variables deep inside
   *  another node.
   *
   * @param exp
   *  Term typechecking options including whether to perform integer bounds
   *  checks on literal integers (checkRefinement).
   */
  case class Options(
    callsReturnLocals: Boolean = false,
    exp: term.Check.Options = term.Check.Options()
  )

  /** Get the value environment for a given local method result storage struct.
   * This is usually just the method's return values. If we enable sneaky
   * invariant mode (callsReturnLocals) then the caller is able to inspect all
   * of the called method's local variables, including nested calls.
   */
  def heapOfStorage(env: Env, prefix: names.Prefix, storage: Storage, options: Options): term.Check.Env =
    val pfx = names.Prefix(prefix.prefix ++ List(storage.name))
    val c = except.getEntry("class", storage.klass, env.classes)
    val m = except.getEntry("method", storage.method, c.methodsMap)

    if !options.callsReturnLocals
    then SortedMap.from(
        m.returns.map { kv =>
          pfx(kv.name) -> kv.sort
        })
    else SortedMap.from(
        (m.params ++ m.returns ++ m.locals).map { kv =>
          pfx(kv.name) -> kv.sort
        }) ++
        m.storageMap.flatMap(s => heapOfStorage(env, pfx, s._2, options))

  def statement(env: Env, m: Method, s: Statement, options: Options): Unit = s match
    case Statement.Assign(x, e) =>
      val xs = except.getEntry("variable",
        names.Ref.fromComponent(x), env.values)
      val es = term.Check.exp(env.values, e, options.exp)
      except.assertEqual(s.ppr, xs, es)
    case Statement.AssignSelf(x, e) =>
      val xs = except.getEntry("field",
        x, env.self.fieldsMap)
      val es = term.Check.exp(env.values, e, options.exp)
      except.assertEqual(s.ppr, xs, es)
    case Statement.Ite(p, t, f) =>
      val ps = term.Check.exp(env.values, p, options.exp)
      except.assertEqual(p.ppr, ps, Sort.Bool)
      statement(env, m, t, options)
      statement(env, m, f, options)
    case Statement.Seq(p, q) =>
      statement(env, m, p, options)
      statement(env, m, q, options)
    case Statement.Skip =>
    case c: Statement.Call =>
      val i = except.getEntry("instance",
        c.instance, env.self.objectsMap)
      val k = except.getEntry("class",
        c.klass, env.classes)
      val target = except.getEntry("method",
        c.method, k.methodsMap)

      c.args.zip(target.params).foreach { case (a,p) =>
        val as = term.Check.exp(env.values, a, options.exp)
        except.assertEqual(
          pretty.text(s"method call ${c.klass.pprString}::${c.method.pprString} parameter ${p.name.pprString} bound to") <+> a.ppr,
          as, p.sort)
      }

      c.storage match
        case None =>
        case Some(s) =>
          val st = except.getEntry("storage", s, m.storageMap)
          if st.klass != c.klass || st.method != c.method
          then throw new except.CheckException(
            s"method call ${c.klass.pprString}::${c.method.pprString} tried to store result in ${s.pprString} of type ${st.klass.pprString}::${st.method.pprString} ")

  def method(env: Env, m: Method, options: Options): Unit =
    try
      val allNames =
        (m.params ++ m.returns ++ m.locals).map { kv => kv.name -> kv.ppr} ++
        m.storage.map { s => s.name -> s.ppr }
      val distinct =
        MultiMap(allNames.map { kv => kv._1 -> List(kv._2) } : _*).entries
        .filter { kv => kv._2.length > 1 }

      if (distinct.nonEmpty) {
        throw new except.DuplicateVariablesException(distinct.map(_._2).toList)
      }

      val v0 = env.values
      val v1 = SortedMap.from((m.params ++ m.returns ++ m.locals).map { kv =>
        names.Ref.fromComponent(kv.name) -> kv.sort
      })
      val v2 = m.storage.map(heapOfStorage(env, names.Prefix(List()), _, options))
        .fold(SortedMap.empty[names.Ref, Sort])(_ ++ _)

      val envX = env.copy(values = v0 ++ v1 ++ v2)
      statement(envX, m, m.body, options)
    catch
      case e: Exception =>
        throw new except.InMethod(env.self, m, e)

  def klass(
    classes: names.immutable.RefMap[Class],
    self: Class,
    options: Options
  ): Unit =
    try
      val pfx = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("self"))))
      val v0 = SortedMap.from(self.fields.map { kv =>
        pfx(kv.name) -> kv.sort
      })
      val env = Env(values = v0, classes, self)
      self.methods.foreach { m =>
        method(env, m, options)
      }
    catch
      case e: Exception =>
        throw new except.InClass(self, e)

  def program(
    program: Program,
    options: Options
  ): Unit = program.classes.foreach { c =>
    klass(program.classesMap, c, options)
  }

  object except:
    class CheckException(msg: String) extends Exception(msg)

    class InMethod(k: Class, m: Method, exception: Exception) extends Exception(
      s"\nIn method ${k.name.pprString}::${m.name.pprString}.", exception)

    class InClass(k: Class, exception: Exception) extends Exception(
      s"\nIn class ${k.name.pprString}.", exception)

    class NoSuchVariableException(x: names.Component, env: term.Check.Env) extends CheckException(
      s"""No such variable ${x.pprString}.
        |Environment: ${names.Namespace.fromMap(env).pprString}""".stripMargin)

    class DuplicateVariablesException(dups: List[List[pretty.Doc]]) extends CheckException(
      s"""Variable name clash. Name shadowing is not permitted.
        |${pretty.layout(pretty.indent(pretty.vsep(dups.map(pretty.tuple(_)))))}""".stripMargin)

    class NoSuchEntryException[K <: pretty.Pretty: scala.math.Ordering, V](
      typ: String,
      entry: K,
      map: scala.collection.immutable.SortedMap[K, V]
    ) extends CheckException(
      s"""No such ${typ} ${entry.pprString} in ${typ} map.
        |Options: ${pretty.layout(pretty.tuple(map.keys.map(_.ppr).toSeq))}""".stripMargin)

    class TypeMismatch(e: pretty.Doc, s: Sort, t: Sort) extends CheckException(
      s"""Type mismatch: ${s.pprString} != ${t.pprString}.
         |In ${pretty.layout(e)}""".stripMargin)

    def assertEqual(p: pretty.Doc, s1: Sort, s2: Sort) =
      if s1 != s2
      then throw new TypeMismatch(p, s1, s2)

    def getEntry[K <: pretty.Pretty: scala.math.Ordering, V](
      typ: String,
      key: K,
      map: scala.collection.immutable.SortedMap[K, V]
    ) =
      map.getOrElse(key,
        throw new NoSuchEntryException(typ, key, map))
