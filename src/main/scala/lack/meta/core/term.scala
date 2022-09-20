package lack.meta.core

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Term-level values and expressions. */
object term:

  /** Values */
  sealed trait Val extends pretty.Pretty:
    /** Check if a value matches a sort.
     *
     * Values are structurally typed, so that the value Val.Int(0) fits type
     * UInt8, Int32, and so on. This means that there isn't exactly one
     * most-general-type for each value. */
    def check(sort: Sort): Boolean

  object Val:
    /** Boolean values. */
    case class Bool(b: Boolean) extends Val:
      def ppr = pretty.text(if (b) "#b'true" else "#b'false")
      def check(sort: Sort) = sort == Sort.Bool

    /** Unbounded integer values.
     *
     * Operations on these use unbounded arithmetic, at least conceptually,
     * but to compile these operations we need to prove that they don't
     * overflow the runtime representation type. */
    case class Int(i: Integer) extends Val:
      def ppr = pretty.text(s"#int'$i")
      def check(sort: Sort) = sort match
        case sort: Sort.Integral =>
          sort.minInclusive <= i && i <= sort.maxInclusive
        case Sort.Subrange(min, max, _) =>
          min <= i && i <= max
        case _ =>
          false

    /** Mathematical real number.
     *
     * These values are logically reals, but the compiled runtime
     * representation is a float, which is a bit of a lie. */
    case class Real(r: num.Real) extends Val:
      def ppr = pretty.string(s"#r'$r")
      def check(sort: Sort) = sort == Sort.Real32

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

    def eval_ii_i(args: List[Val])(f: (Integer, Integer) => Integer): Val = args match
      case List(Val.Int(i), Val.Int(j)) => Val.Int(f(i, j))

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

  /** Pure expressions */
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
  sealed trait Flow extends pretty.Pretty:
    def sort: Sort
  object Flow:
    /** Pure expression */
    case class Pure(e: Exp) extends Flow:
      def ppr  = e.ppr
      def sort = e.sort

    /** x -> y, or "first x then y". */
    case class Arrow(a: Exp, b: Exp) extends Flow:
      require(a.sort == b.sort,
        s"${ppr}\nsorts differ ${a.sort.ppr} /= ${b.sort.ppr}")
      def sort = a.sort
      def ppr = pretty.sexpr(List("flow'->", a.ppr, b.ppr))

    /** Followed by, or initialised delay.
     * Fby(v, e) or in Lustre syntax "v fby e" is equivalent to
     * "v -> pre e". */
    case class Fby(v: term.Val, e: Exp) extends Flow:
      require(v.check(e.sort),
        s"${ppr}\nvalue doesn't support sort ${e.sort.ppr}")
      def sort = e.sort
      def ppr  = pretty.sexpr(List("flow'fby", v.ppr, e.ppr))

    /** Previous value.
     * Pre(e) is equivalent to Fby(undefined, e) for some fresh undefined
     * value.
     * Having this as a separate primitive might make pretty-printing a little
     * bit nicer, but I'm not sure whether it's worth it.
     */
    case class Pre(e: Exp) extends Flow:
      def sort = e.sort
      def ppr  = pretty.sexpr(List("flow'pre", e.ppr))

    def app(sort: Sort, prim: term.Prim, args: Exp*) =
      Flow.Pure(Exp.App(sort, prim, args : _*))
    def var_(sort: Sort, v: names.Ref) =
      Flow.Pure(Exp.Var(sort, v))
    def val_(sort: Sort, v: term.Val) =
      Flow.Pure(Exp.Val(sort, v))
