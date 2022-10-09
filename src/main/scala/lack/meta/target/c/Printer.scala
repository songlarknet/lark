package lack.meta.target.c

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given

import lack.meta.core.Sort
import lack.meta.core.term
import lack.meta.core.term.{Exp, Val}
import lack.meta.core.node.{Node, Schedule, Variable}

import lack.meta.core.obc
import lack.meta.core.obc.Obc.{Statement, Method, Class}

import scala.collection.immutable.SortedMap

/** Pretty-printing helpers for C */
object Printer:

  object Decl:
    /** Declare a struct */
    def struct(n: names.Ref, fields: List[pretty.Doc]): pretty.Doc =
      pretty.text("typedef struct {") <@>
        pretty.indent(pretty.vsep(fields)) <@>
      pretty.text("}") <+> Ident.ref(n) <> pretty.semi

    /** Declare a local variable or struct field */
    def var_(n: names.Component, typ: pretty.Doc): pretty.Doc =
      typ <+> Ident.component(n) <> pretty.semi
    def var_(n: names.Component, typ: names.Ref): pretty.Doc =
      var_(n, Ident.ref(typ))
    def var_(n: names.Component, typ: Sort): pretty.Doc =
      var_(n, Type.sort(typ))

    /** Function prototype */
    def fun(returns: pretty.Doc, name: names.Ref, params: List[pretty.Doc]) =
      returns <+> Ident.ref(name) <> pretty.tuple(params) <> pretty.semi

  /** References to types */
  object Type:
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

  object Term:
    def address(ptr: pretty.Doc): pretty.Doc =
      pretty.ampersand <> ptr

    def fieldptr(ptr: pretty.Doc, field: pretty.Doc): pretty.Doc =
      ptr <> "->" <> field
    def fieldptr(ptr: pretty.Doc, field: names.Component): pretty.Doc =
      fieldptr(ptr, Ident.component(field))

    def field(struct: pretty.Doc, field: names.Component): pretty.Doc =
      struct <> "." <> Ident.component(field)

    def fun(name: pretty.Doc, args: List[pretty.Doc]): pretty.Doc =
      name <> pretty.tuple(args)
    def fun(name: names.Ref, args: List[pretty.Doc]): pretty.Doc =
      fun(Ident.ref(name), args)

    def var_(name: names.Component): pretty.Doc =
      Ident.component(name)

    def fields(path: List[names.Component], name: names.Component): pretty.Doc =
      pretty.ssep((path :+ name).map(Ident.component(_)), pretty.dot)

    /** Pretty-print a value */
    def val_(v: Val): pretty.Doc = v match
      case Val.Bool(b) => b.toString
      case Val.Refined(s: Sort.BoundedInteger, Val.Int(i)) =>
        val suffix = (s.signed, s.width) match
          case (true,  64) => "ll"
          case (false, 64) => "ull"
          case (true,  32) => "l"
          case (false, 32) => "ul"
          case (_,     _)  => ""
        pretty.value(i) <> suffix
      case Val.Real(r) => pretty.value(r) <> "f"
      case _ =>
        throw new except.BigNumberException("value", v.ppr)

  object Stm:
    def block(stms: pretty.Doc) =
      pretty.text("{") <@> pretty.indent(stms) <@> pretty.text("}")

    def assign(lhs: pretty.Doc, rhs: pretty.Doc) =
      lhs <+> pretty.equal <+> rhs <> pretty.semi

    def if_(pred: pretty.Doc, then_ : pretty.Doc, else_ : Option[pretty.Doc]) =
      pretty.text("if") <+> pretty.parens(pred) <+> block(then_) <>
      (else_ match
        case None => pretty.emptyDoc
        case Some(s) => pretty.space <> pretty.text("else") <+> block(s))

    def fun(name: names.Ref, args: List[pretty.Doc]): pretty.Doc =
      Term.fun(Ident.ref(name), args) <> pretty.semi

    def assert(cond: pretty.Doc): pretty.Doc =
      Term.fun(pretty.text("assert"), List(cond)) <> pretty.semi

    def assertEquals(one: pretty.Doc, other: pretty.Doc, sort: Sort): pretty.Doc =
      val cond = sort match
        case Sort.Real =>
          Term.fun("lack_float_approx", List(one, other))
        case _ =>
          one <+> pretty.text("==") <+> other
      assert(cond)

  /** Identifiers
   * Properties we want:
   * *  "nice" identifiers containing only alpha, digit and underscore should be passed as-is
   * * encode is injective
   * * encode contains only alpha, digit, underscore and dollar
   * * I don't care how ugly other chars get
   * * keywords get encoded to non-keywords
   *
   * Examples:
   * > component(grebe)       = grebe
   * > component(grebe?0)     = grebe$0
   * > component(name<weird>) = $$name$$3cweird$$3e
   * > component(if)          = $$if
   * > ref(crested.grebe)     = crested$grebe
   * > ref(crested.grebe?1)   = crested$grebe$1
   * > ref(cre$ted?0.grebe)   = cre$$24ted$0$grebe
   */
  object Ident:

    def suffix(ref: names.Ref, suffix: String): names.Ref = names.Ref(
      ref.fullyQualifiedPath,
      names.Component(names.ComponentSymbol.fromScalaSymbol(suffix)))

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
      if enc.length == s.length && !blacklist(s)
      then s
      else "$$" + enc

    def encodeChar(c: Char): String =
      if c.isLetter || c.isDigit || c == '_'
      then c.toString
      else "$$" + f"${c.toInt}%02X"

    def freshen(base: String, used: List[names.Component]): pretty.Doc =
      val baseS = base
      val usedS = used.map(componentString(_))
      if !usedS.contains(baseS)
      then pretty.text(baseS)
      else if !usedS.contains("$$" + baseS)
      then pretty.text("$$" + baseS)
      else
        val fresh =
          for
            k <- 1 to 100
            baseK = baseS + "$" + k
            if !usedS.contains(baseK)
          yield pretty.text(baseK)
        fresh.headOption.getOrElse(
          throw new Exception(s"Can't generate free variable for ${base} while avoiding set ${usedS}"))

    /** Don't use these as variables. */
    val keywords = Set(
      // Keywords
      "_Alignas", "_Alignof", "_Bool", "_Generic", "_Complex", "_Imaginary",
      "_Static_assert", "__alignof", "__alignof__", "__asm", "__asm__", "__attribute",
      "__attribute__", "__builtin_va_arg", "__builtin_offsetof", "__const",
      "__const__", "__extension__", "__inline", "__inline__", "__packed__", "__restrict",
      "__restrict__", "__signed", "__signed__", "__volatile", "__volatile__", "asm",
      "auto", "break", "case", "char", "const", "continue", "default", "do", "double",
      "else", "enum", "extern", "float", "for", "goto", "if", "inline", "_Noreturn",
      "int", "long", "register", "restrict", "return", "short", "signed", "sizeof",
      "static", "struct", "switch", "typedef", "union", "unsigned", "void",
      "volatile", "while",
      // Base functions that shouldn't be shadowed
      "assert")
    def blacklist(string: String): Boolean =
      keywords.contains(string) ||
        string.startsWith("lack_")

  object except:
    class BigNumberException(typ: String, doc: pretty.Doc) extends Exception(
      s"""Arbitrary-precision integers can't be compiled to C.
          |${typ}: ${pretty.layout(doc)}
          |""".stripMargin)