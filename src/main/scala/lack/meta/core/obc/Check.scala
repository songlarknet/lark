package lack.meta.core.obc

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given

import lack.meta.core.Sort
import lack.meta.core.term.Exp
import lack.meta.core.term

import lack.meta.core.obc.Obc.{Statement, Method, Class}

import scala.collection.immutable.SortedMap

/** Typechecking for Obc, the imperative object language */
object Check:

  case class Env(
    values: term.Check.Env,
    classes: names.immutable.RefMap[Class],
    self: Class
  )

  case class Options(
    exp: term.Check.Options = term.Check.Options()
  )

  def statement(env: Env, s: Statement, options: Options): Unit = s match
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
      statement(env, t, options)
      statement(env, f, options)
    case Statement.Seq(p, q) =>
      statement(env, p, options)
      statement(env, q, options)
    case Statement.Skip =>
    case c: Statement.Call =>
      val i = except.getEntry("instance",
        c.instance, env.self.objectsMap)
      val k = except.getEntry("class",
        c.klass, env.classes)
      val m = except.getEntry("method",
        c.method, k.methodsMap)

      c.assigns.zip(m.returns).foreach { case (o,r) =>
        val os = except.getEntry("variable",
          names.Ref.fromComponent(o), env.values)
        except.assertEqual(
          pretty.text(s"method call ${c.klass}::${c.method} return value ${r.name} bound to ${o}"),
          os, r.sort)
      }

      c.args.zip(m.params).foreach { case (a,p) =>
        val as = term.Check.exp(env.values, a, options.exp)
        except.assertEqual(
          pretty.text(s"method call ${c.klass}::${c.method} parameter ${p.name} bound to") <+> a.ppr,
          as, p.sort)
      }

  def method(env: Env, m: Method, options: Options): Unit =
    try
      val v0 = env.values
      val v1 = SortedMap.from((m.params ++ m.returns ++ m.locals).map { kv =>
        names.Ref.fromComponent(kv.name) -> kv.sort
      })
      val envX = env.copy(values = v0 ++ v1)
      statement(envX, m.body, options)
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

  object except:
    class CheckException(msg: String) extends Exception(msg)

    class InMethod(k: Class, m: Method, exception: Exception) extends Exception(
      s"\nIn method ${k.name.pprString}::${m.name.pprString}.", exception)

    class InClass(k: Class, exception: Exception) extends Exception(
      s"\nIn class ${k.name.pprString}.", exception)

    class NoSuchVariableException(x: names.Component, env: term.Check.Env) extends CheckException(
      s"""No such variable ${x.pprString}.
        |Environment: ${names.Namespace.fromMap(env).pprString}""".stripMargin)

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

  def program(
    classes: names.immutable.RefMap[Class],
    options: Options
  ): Unit = classes.foreach { case (k,c) =>
    klass(classes, c, options)
  }
