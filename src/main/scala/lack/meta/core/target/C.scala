package lack.meta.core.target

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given

import lack.meta.core.Sort
import lack.meta.core.term
import lack.meta.core.term.{Exp, Val}
import lack.meta.core.node.{Node, Schedule, Variable}

import lack.meta.core.obc.Obc.{Statement, Method, Class}

import scala.collection.immutable.SortedMap

/** Translating from Obc to C */
object C:

  case class Options(
    basename: String,
    classes:  names.immutable.RefMap[Class],
    includes: List[String] = List("#include <lack.h>"),
    version: String = "v0" // TODO
  )

  def header(options: Options): pretty.Doc =
    prelude(options) <@>
    pretty.vsep(options.classes.values.map(Header.klass(_)).toSeq)

  def source(options: Options, selfInclude: Boolean = true): pretty.Doc =
    val includes =
      if selfInclude
      then options.includes ++ List(s"#include \"${options.basename}.h\"")
      else options.includes
    prelude(options.copy(includes = includes)) <@>
    pretty.vsep(options.classes.values.map(Source.klass(_, options)).toSeq)

  def prelude(options: Options): pretty.Doc =
    val text =
      s"${options.basename} generated by lack version ${options.version}"
    val txxt = text.map(c => '*')
    val lines = List(
      s"/***${txxt}**/",
      s"/** ${text} */",
      s"/***${txxt}**/",
      "") ++ options.includes ++ List("")
    pretty.vsep(lines.map(pretty.text(_)))

  object Base:
    def state(klass: names.Ref): names.Ref = names.Ref(
      klass.fullyQualifiedPath,
      names.Component(names.ComponentSymbol.fromScalaSymbol("state")))

    def out(name: names.Ref): names.Ref = names.Ref(
      name.fullyQualifiedPath,
      names.Component(names.ComponentSymbol.fromScalaSymbol("out")))

    def sort(s: Sort): pretty.Doc = s match
      case Sort.Bool => "bool"
      case b: Sort.BoundedInteger => pretty.text(
        (if b.signed then "int" else "uint") +
        b.width.toString + "_t")
      case Sort.Real =>
        // TODO UNSOUND: compiling reals to floats for now
        pretty.text("float32_unsound_t")
      case Sort.ArbitraryInteger =>
        throw new except.BigNumberException("Sort", s.ppr)

    val void = pretty.text("void")

    def ptr(doc: pretty.Doc): pretty.Doc =
      doc <> "*"

    def deref(ptr: pretty.Doc, field: pretty.Doc): pretty.Doc =
      ptr <> "->" <> field

    def field(struct: pretty.Doc, field: pretty.Doc): pretty.Doc =
      struct <> "." <> field

  object Header:
    def struct(n: names.Ref, fields: pretty.Doc): pretty.Doc =
      pretty.text("typedef struct {") <@>
        pretty.indent(fields) <@>
      pretty.text("}") <+> Ident.ref(n) <> pretty.semi

    def state(k: Class): pretty.Doc =
      val objectsP = k.objects.map { case (k,v) =>
        Ident.ref(Base.state(v)) <+> Ident.component(k) <> pretty.semi
      }
      val fieldsP = k.fields.map { kv =>
        Base.sort(kv.sort) <+> Ident.component(kv.name) <> pretty.semi
      }

      struct(Base.state(k.name),
        pretty.vsep(objectsP ++ fieldsP))

    def method(k: Class, m: Method): pretty.Doc =
      val name = names.Ref(k.name.fullyQualifiedPath, m.name)

      val (struct_decl, ret_ty, ret_args) = m.returns match
        case List() => (List(), Base.void, List())
        case List(r) => (List(), Base.sort(r.sort), List())
        case rets =>
          val fieldsP = rets.map { kv =>
            Base.sort(kv.sort) <+> Ident.component(kv.name) <> pretty.semi
          }
          val out = struct(Base.out(name),
            pretty.vsep(fieldsP))
          (List(out), Base.void, List(Base.ptr(Ident.ref(Base.out(name)))))

      val argsP =
        Base.ptr(Ident.ref(Base.state(k.name))) ::
          m.params.map { kv => Base.sort(kv.sort) <+> Ident.component(kv.name) } ++
          ret_args

      pretty.vsep(
        struct_decl ++
        List(ret_ty <+> Ident.ref(name) <> pretty.tuple(argsP) <> pretty.semi)
      ) <> pretty.line

    def klass(k: Class): pretty.Doc =
      val methods = k.methods.map(method(k, _))
      state(k) <@>
        pretty.vsep(methods) <> pretty.line

  object Source:
    def freshen(base: String, used: List[names.Component]) =
      val baseS = base
      val usedS = used.map(Ident.componentString)
      if !usedS.contains(baseS)
      then pretty.text(baseS)
      else
        val fresh =
          for
            k <- 1 to 100
            baseK = baseS + "$" + k
            if !usedS.contains(baseK)
          yield pretty.text(baseK)
        fresh.headOption.getOrElse(
          throw new Exception(s"Can't generate free variable for ${base} in set ${usedS}"))

    def val_(v: Val): pretty.Doc = v match
      case Val.Bool(b) => b.toString
      case Val.Refined(s: Sort.BoundedInteger, Val.Int(i)) =>
        val suffix = (s.signed, s.width) match
          case (true,  64) => "ul"
          case (false, 64) => "l"
          case (true,  32) => "u"
          case (_,     _)  => ""
        pretty.value(i) <> suffix
      case Val.Real(r) => pretty.value(r)
      // TODO hmm
      case Val.Int(i) =>
        pretty.value(i)
      case _ =>
        throw new except.BigNumberException("value", v.ppr)

    def binop(prim: term.Prim): (String, Int) =
      import term.prim.Table._
      prim match
        case Or  => ("||", 12)
        case And => ("&&", 11)
        case Lt  => ("<",  6)
        case Le  => ("<=", 6)
        case Gt  => (">",  6)
        case Ge  => (">",  6)
        case Eq  => ("==", 6)
        case Add => ("+",  4)
        case Sub => ("-",  4)
        case Mul => ("*",  3)
        case Div => ("/",  3)
    val COMMA_PREC = 15
    val PARENS_PREC = 16

    //   10 +  2 * 5   < 10
    // ((10 + (2 * 5)) < 10)
    // a +  b + c
    // a + (b + c)
    def nest(self: pretty.Doc, e: Exp, p: Int, limit: Int) =
      if p <= limit
      then pretty.parens(exp(self, e, PARENS_PREC))
      else exp(self, e, p)

    def exp(self: pretty.Doc, e: Exp, p: Int): pretty.Doc = e match
      case Exp.Var(_, r) => r.prefix match
        case self_
         if self_ == Class.self.prefix =>
          Base.deref(self, Ident.component(r.name))
        case List() =>
          Ident.component(r.name)
        case _ =>
          lack.meta.base.assertions.impossible(
            "Ill-formed variable reference in Obc expression",
            "exp" -> e)
      case Exp.Val(_, v) => val_(v)

      // TODO: do we need to insert casts?
      case Exp.Cast(_, e) =>
        exp(self, e, p)

      case Exp.App(_, term.prim.Table.Negate, a) =>
        pretty.text("-") <> nest(self, a, p, 2)
      case Exp.App(_, term.prim.Table.Not, a) =>
        pretty.text("!") <> nest(self, a, p, 2)
      case Exp.App(_, term.prim.Table.Implies, a, b) =>
        pretty.text("lack_implies") <> pretty.tuple(List(exp(self, a, COMMA_PREC), exp(self, b, COMMA_PREC)))
      case Exp.App(_, op, a, b) =>
        val (o, pp) = binop(op)
        nest(self, a, p, pp) <+> o <+> nest(self, b, p, pp + 1)
      case Exp.App(_, term.prim.Table.Ite, pred, t, f) =>
        nest(self, pred, p, 13) <+> "?" <+>
          nest(self, t, p, 13) <+> ":" <+>
          nest(self, f, p, 13)
      case Exp.App(_, p, _ : _*) =>
        throw new Exception(s"prim not supported: ${p}")

    def exp(self: pretty.Doc, e: Exp): pretty.Doc = exp(self, e, PARENS_PREC)

    def statement(self: pretty.Doc, s: Statement, options: Options): pretty.Doc = s match
      case Statement.Assign(name, e) =>
        Ident.component(name) <+> pretty.equal <+> exp(self, e) <> pretty.semi
      case Statement.AssignSelf(name, e) =>
        Base.deref(self, Ident.component(name)) <+> pretty.equal <+> exp(self, e) <> pretty.semi
      case Statement.Ite(p, t, f) =>
        val else_ = f match
          case Statement.Skip => pretty.emptyDoc
          case _ => pretty.text("else") <+> "{" <@>
            pretty.indent(statement(self, f, options)) <@>
           "}"

        pretty.text("if") <+> pretty.parens(exp(self, p)) <+> "{" <@>
          pretty.indent(statement(self, t, options)) <@>
        "}" <> else_
      case Statement.Call(assigns, klass, method, instance, args) =>
        val name  = names.Ref(klass.fullyQualifiedPath, method)
        val nameP = Ident.ref(name)
        val instP = Base.deref(self, Ident.component(instance))
        val argsP = args.map(exp(self, _))
        assigns match
          case List() =>
            nameP <> pretty.tuple(instP :: argsP) <> pretty.semi
          case List(o) =>
            Ident.component(o) <+> pretty.equal <+> nameP <> pretty.tuple(instP :: argsP) <> pretty.semi
          case _ =>
            val outT = Ident.ref(Base.out(name))
            val outV = Ident.component(instance)
            val meth = options.classes(klass).methods.find(_.name == method).get
            val assignsP = assigns.zip(meth.returns).map { case (a, r) =>
              Ident.component(a) <+> pretty.equal <+> Base.field(outV, Ident.component(r.name)) <> pretty.semi
            }
            outT <+> outV <> pretty.semi <@>
              nameP <> pretty.tuple(instP :: argsP ++ List(pretty.ampersand <> outV)) <> pretty.semi <@>
              pretty.vsep(assignsP)

      case Statement.Seq(p, q) =>
        statement(self, p, options) <@> statement(self, q, options)
      case Statement.Skip => pretty.emptyDoc


    def method(k: Class, m: Method, options: Options): pretty.Doc =
      val name = names.Ref(k.name.fullyQualifiedPath, m.name)
      val used = (m.params ++ m.returns ++ m.locals).map(_.name)
      val self = freshen("self", used)
      val out  = freshen("out", used)

      val (ret_ty, ret_args, ret_stms) = m.returns match
        case List() =>
          (Base.void, List(), List())
        case List(r) =>
          val stm = pretty.text("return") <+> Ident.component(r.name) <> pretty.semi
          (Base.sort(r.sort), List(), List(stm))
        case rets =>
          val stms = rets.map { r =>
            Base.deref(out, Ident.component(r.name)) <+> pretty.equal <+> Ident.component(r.name) <> pretty.semi
          }
          (Base.void, List(Base.ptr(Ident.ref(Base.out(name))) <+> out), stms)

      val argsP =
        (Base.ptr(Ident.ref(Base.state(k.name))) <+> self) ::
          m.params.map { kv => Base.sort(kv.sort) <+> Ident.component(kv.name) } ++
          ret_args

      val allocs = (m.locals ++ m.returns).map { case kv =>
        Base.sort(kv.sort) <+> Ident.component(kv.name) <> pretty.semi
      }

      val stms =
        allocs ++
        List(Source.statement(self, m.body, options)) ++
        ret_stms

      ret_ty <+> Ident.ref(name) <> pretty.tuple(argsP) <@>
        pretty.text("{") <@>
        pretty.indent(
          pretty.vsep(stms)
        ) <@>
        pretty.text("}") <@>
        pretty.emptyDoc

    def klass(k: Class, options: Options): pretty.Doc =
      val methods = k.methods.map(method(k, _, options))
      pretty.vsep(methods)

  /** Identifiers
   * Properties we want:
   * *  "nice" identifiers containing only alpha, digit and underscore should be passed as-is
   * * encode is injective
   * * encode contains only alpha, digit, underscore and dollar
   * * I don't care how ugly other chars get
   *
   * Examples:
   * > component(grebe)       = grebe
   * > component(grebe?0)     = grebe$0
   * > component(name<weird>) = $$name$$3cweird$$3e
   * > ref(crested.grebe)     = crested$grebe
   * > ref(crested.grebe?1)   = crested$grebe$1
   * > ref(cre$ted?0.grebe)   = cre$$24ted$0$grebe
   */
  object Ident:
    /** Pretty-print a qualified identifier. */
    def ref(r: names.Ref): pretty.Doc =
      r.fullyQualifiedPath.map(componentString(_)).mkString("$")

    /** Pretty-print a simple identifier. */
    def component(c: names.Component): pretty.Doc =
      componentString(c)

    def componentString(c: names.Component): String =
      encode(c.symbol.toString) + (c.ix.fold("")(i => "$" + i))

    def encode(s: String): String =
      val enc = s.flatMap(encodeChar(_))
      if enc.length == s.length
      then s
      else "$$" + enc

    def encodeChar(c: Char): String =
      if c.isLetter || c.isDigit || c == '_'
      then c.toString
      else "$$" + f"${c.toInt}%02X"

  object except:
    class BigNumberException(typ: String, doc: pretty.Doc) extends Exception(
      s"""Arbitrary-precision integers can't be compiled to C.
          |${typ}: ${pretty.layout(doc)}
          |""".stripMargin)