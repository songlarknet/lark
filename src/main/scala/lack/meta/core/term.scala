package lack.meta.core

import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

object term:

  sealed trait Val extends pretty.Pretty:
    def check(sort: Sort): Boolean

  object Val:
    case class Bool(b: Boolean) extends Val:
      def ppr = pretty.text(if (b) "#b'true" else "#b'false")
      def check(sort: Sort) = sort == Sort.Bool

    case class Int(i: Integer) extends Val:
      def ppr = pretty.text(s"#int'$i")
      def check(sort: Sort) = sort match
        case sort: Sort.Integral =>
          sort.minInclusive <= i && i <= sort.maxInclusive
        case Sort.Subrange(min, max, _) =>
          min <= i && i <= max
        case _ =>
          false

    case class Mod(i: Integer, width: Sort.Mod) extends Val:
      def ppr = pretty.string(s"#mod${width.width}'$i")
      def check(sort: Sort) = sort match
        case m: Sort.Mod =>
          m.range.contains(i) && m.width == width.width
        case _ =>
          false

    case class Float32(r: Float) extends Val:
      def ppr = pretty.string(s"#f32'$r")
      def check(sort: Sort) = sort == Sort.Float32

    /** Logical real with float32 runtime representation */
    case class Real32(r: Float) extends Val:
      def ppr = pretty.string(s"#r32'$r")
      def check(sort: Sort) = sort == Sort.Real32

    case class Struct(fields: List[(String, Val)], struct: Sort.Struct) extends Val:
      require(fields.map(_._1) == struct.fields.map(_._1))
      require(struct.fields.zip(fields).forall(f => f._2._2.check(f._1._2)))
      def ppr = pretty.parens(struct.ppr <+> pretty.hsep(fields.map(f => pretty.text(s":${f._1}") <+> f._2.ppr)))
      def check(sort: Sort) = sort == struct

  /** Pure total primitives. */
  trait Prim extends pretty.Pretty:
    // TODO: prims need sort checking
    // def sort(args: List[Sort]): Sort
    def eval(args: List[Val]): Val
  object Prim:

    abstract class Simple(prim: String, expect: List[Sort], ret: Sort) extends Prim:
      def ppr = pretty.text(prim)

    case object And extends Simple("and", List(Sort.Bool, Sort.Bool), Sort.Bool):
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(a && b)
    case object Or  extends Simple("or", List(Sort.Bool, Sort.Bool), Sort.Bool):
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(a || b)
    case object Not extends Simple("not", List(Sort.Bool), Sort.Bool):
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(a)) => Val.Bool(!a)
    case object Implies extends Simple("=>", List(Sort.Bool, Sort.Bool), Sort.Bool):
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(if (a) b else true)

    case object Ite extends Prim:
      def ppr = pretty.text("ite")
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(p), t, f) => if (p) t else f

    case object Negate extends Prim:
      def ppr = pretty.text("negate")
      def eval(args: List[Val]): Val = args match
        case List(Val.Int(i)) => Val.Int(- i)

    // TODO: floats too
    def eval_ii_b(args: List[Val])(f: (Integer, Integer) => Boolean): Val = args match
      case List(Val.Int(i), Val.Int(j)) => Val.Bool(f(i, j))
      case List(Val.Mod(i, _), Val.Mod(j, _)) => Val.Bool(f(i, j))

    def eval_ii_i(args: List[Val])(f: (Integer, Integer) => Integer): Val = args match
      case List(Val.Int(i), Val.Int(j)) => Val.Int(f(i, j))
      case List(Val.Mod(i, iw), Val.Mod(j, jw)) =>
        require(iw.width == jw.width)
        val r = f(i, j)
        Val.Mod(r & iw.range.max, iw)

    case object Add extends Prim:
      def ppr = pretty.text("+")
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ + _))

    case object Sub extends Prim:
      def ppr = pretty.text("-")
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ - _))

    case object Mul extends Prim:
      def ppr = pretty.text("*")
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ * _))

    /** "Safe" division where x / 0 = 0, which agrees with Isabelle and Z3 semantics
     * for integers. However, SMTLib's bitvector semantics for division are that bvudiv
     * returns a bitvector with all ones. For signed division with bvsdiv, the result
     * is -1 or 1 depending on the sign of the left-hand-side.
     * We probably want to wrap bv.div to keep the x/0=0 semantics.
     * TODO: wrap bitvector division in smt encoding
     */
    case object Div extends Prim:
      def ppr = pretty.text("/")
      def eval(args: List[Val]): Val = eval_ii_i(args) {
        case (i, j) => if (j == 0) 0 else (i / j)
      }

    case object Eq extends Prim:
      def ppr = pretty.text("=")
      def eval(args: List[Val]): Val = args match
        case List(i, j) => Val.Bool(i == j)

    case object Le extends Prim:
      def ppr = pretty.text("<=")
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ <= _))

    case object Lt extends Prim:
      def ppr = pretty.text("<")
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ < _))

    case object Ge extends Prim:
      def ppr = pretty.text(">=")
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ >= _))

    case object Gt extends Prim:
      def ppr = pretty.text(">")
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ > _))

    case class StructGet(field: String, struct: Sort.Struct) extends Prim:
      require(struct.fields.map(_._1).contains(field))

      def ppr = struct.ppr <> pretty.squote <> pretty.text(field)
      def eval(args: List[Val]): Val = args match
        case List(vstr: Val.Struct) =>
          require(vstr.struct == struct)
          vstr.fields.filter(v => v._1 == field).head._2

    case class StructMk(struct: Sort.Struct) extends Prim:
      def ppr = struct.ppr
      def eval(args: List[Val]): Val =
        Val.Struct(struct.fields.map(_._1).zip(args).toList, struct)

  sealed trait Exp extends pretty.Pretty:
    // Annotate each node with its type. Is this overkill? The expressions probably won't be "too big"...
    def sort: Sort

  object Exp:
    /** Variable */
    case class Var(sort: Sort, v: names.Ref) extends Exp:
      def ppr = v.ppr

    /** Value */
    case class Val(sort: Sort, v: term.Val) extends Exp:
      def ppr = v.ppr

    /** Pure primitive application */
    case class App(sort: Sort, prim: term.Prim, args: Exp*) extends Exp:
      // TODO: should constructors do typechecking?
      def ppr = pretty.sexpr((prim :: args.toList).map(_.ppr))

    /** Streaming terms */
    object flow:
      /** Previous value */
      case class Pre(sort: Sort, e: Exp) extends Exp:
        def ppr = pretty.sexpr(List("flow'pre", e.ppr))
      /** x -> y, or "first x then y". */
      case class Arrow(sort: Sort, a: Exp, b: Exp) extends Exp:
        def ppr = pretty.sexpr(List("flow'->", a.ppr, b.ppr))

      /** Followed by, or initialised delay.
       * Fby(v, e) or in Lustre syntax "v fby e" is equivalent to
       * "v -> pre e".
       * This primitive has a slightly better encoding.
       * Vélus also only supports fby and not pre, so we'll need to
       * rewrite occurrences of pre to fby if we want to generate Vélus.
       */
      case class Fby(sort: Sort, v: term.Val, e: Exp) extends Exp:
        def ppr = pretty.sexpr(List("flow'fby", v.ppr, e.ppr))
