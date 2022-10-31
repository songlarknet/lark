package lark.meta.core.term.prim

import lark.meta.base.num
import lark.meta.base.num.{Integer, Real}
import lark.meta.base.{names, pretty}
import lark.meta.core.Sort
import lark.meta.core.term.{Prim, Val}
import lark.meta.core.term.Prim.{Simple, Prim_nn_n, Prim_nn_b, CheckException, EvalException}

/** Primitive definitions and table.
 * Make sure to add any newly-defined primitives to Table.table and generators
 * to src/test/scala/lark/meta/core/term/prim/G.scala.
 */
object Table:

  /** Table of all base primitives.
    * These are the primitives that operate on base types and take no static
    * arguments.
    *
    * Later, if we have primitives for record constructors and accessors, then
    * those primitives will be dependent on the set of types in the program. */
  val base : List[Prim] = List(
    And, Or, Not, Implies,
    Ite,
    Negate,
    Add, Sub, Mul, Div,
    Le, Lt, Ge, Gt, Eq
  )

  /** Operator precedence based on C and Scala */
  object Precedence:
    def unop(prim: Prim): Option[(String, Int)] =
      prim match
        case Negate => Some(("-", UNARY_PREC))
        case Not    => Some(("!", UNARY_PREC))
        case _      => None

    def binop(prim: Prim): Option[(String, Int)] =
      prim match
        // Scala treats ==> as same level as ==, but using the textual operator
        // "implies" has a good precedence.
        case Implies
                 => Some(("implies", 125))
        case Or  => Some(("||",  120))
        case And => Some(("&&",  110))
        case Lt  => Some(("<",    60))
        case Le  => Some(("<=",   60))
        case Gt  => Some((">",    60))
        case Ge  => Some((">=",   60))
        case Eq  => Some(("==",   60))
        case Add => Some(("+",    40))
        case Sub => Some(("-",    40))
        case Mul => Some(("*",    30))
        case Div => Some(("/",    30))
        case _   => None

    val UNARY_PREC   =  20
    val TERNARY_PREC = 130
    val COMMA_PREC   = 150
    val PARENS_PREC  = 160


  case object And extends Simple("and", List(Sort.Bool, Sort.Bool), Sort.Bool):
    def evalX(args: List[Val]): Val = args match
      case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(a && b)
      case _ => throw EvalException.impossible(this, args)

  case object Or extends Simple("or", List(Sort.Bool, Sort.Bool), Sort.Bool):
    def evalX(args: List[Val]): Val = args match
      case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(a || b)
      case _ => throw EvalException.impossible(this, args)

  case object Not extends Simple("not", List(Sort.Bool), Sort.Bool):
    def evalX(args: List[Val]): Val = args match
      case List(Val.Bool(a)) => Val.Bool(!a)
      case _ => throw EvalException.impossible(this, args)

  case object Implies extends Simple("=>", List(Sort.Bool, Sort.Bool), Sort.Bool):
    def evalX(args: List[Val]): Val = args match
      case List(Val.Bool(a), Val.Bool(b)) => Val.Bool(if (a) b else true)
      case _ => throw EvalException.impossible(this, args)

  /** Ternary operator, "if-then-else". The name "ite" comes from SMTlib. */
  case object Ite extends Prim:
    def ppr = pretty.text("ite")
    def pprType = "[T]. (Boolean, T, T) => T"

    def sort(args: List[Sort]) = args match
      case List(Sort.Bool, t, f) if t == f =>
        t
      case List(Sort.Bool, t, f) =>
        throw CheckException.exactSame(this, args)
      case _ =>
        throw new CheckException(this, args, "")

    def eval(args: List[Val]): Val = args match
      case List(Val.Bool(p), t, f) => if (p) t else f
      case _ => throw new EvalException(this, args, "")


  case object Negate extends Prim:
    def ppr = pretty.text("negate")
    def pprType = "[T: Numeric]. T => T.logical"

    def sort(args: List[Sort]) = args match
      case List(s) if s.isInstanceOf[Sort.Numeric] =>
        s
      case _ => throw new CheckException(this, args, "")
    def eval(args: List[Val]): Val = args match
      case List(Val.Int(i)) => Val.Int(- i)
      case List(Val.Real(i)) => Val.Real(- i)
      case _ => throw new EvalException(this, args, "")

  case object Add extends Prim_nn_n:
    def ppr = pretty.text("+")
    def int(i: Integer, j: Integer) = i + j
    def real(i: Real, j: Real) = i + j

  case object Sub extends Prim_nn_n:
    def ppr = pretty.text("-")
    def int(i: Integer, j: Integer) = i - j
    def real(i: Real, j: Real) = i - j

  case object Mul extends Prim_nn_n:
    def ppr = pretty.text("*")
    def int(i: Integer, j: Integer) = i * j
    def real(i: Real, j: Real) = i * j

  /** "Safe" division where x / 0 = 0, which agrees with Isabelle and Z3 semantics
   * for integers.
   */
  case object Div extends Prim_nn_n:
    def ppr = pretty.text("/")
    def int(m: Integer, n: Integer) =
      if n == 0
      then 0
      else m / n
    def real(i: Real, j: Real) =
      if j == 0
      then 0
      else i / j

  case object Le extends Prim_nn_b:
    def ppr = pretty.text("<=")
    def int(i: Integer, j: Integer) = i <= j
    def real(i: Real, j: Real) = i <= j

  case object Lt extends Prim_nn_b:
    def ppr = pretty.text("<")
    def int(i: Integer, j: Integer) = i < j
    def real(i: Real, j: Real) = i < j

  case object Ge extends Prim_nn_b:
    def ppr = pretty.text(">=")
    def int(i: Integer, j: Integer) = i >= j
    def real(i: Real, j: Real) = i >= j

  case object Gt extends Prim_nn_b:
    def ppr = pretty.text(">")
    def int(i: Integer, j: Integer) = i > j
    def real(i: Real, j: Real) = i > j

  case object Eq extends Prim:
    def ppr = pretty.text("=")
    def pprType = "[T]. (T,T) => Bool"

    def sort(args: List[Sort]) = args match
      case List(i, j)
        if i == j =>
        Sort.Bool
      case _ =>
        throw CheckException.exactSame(this, args)

    def eval(args: List[Val]): Val = args match
      // TODO-BOUNDED-ARITH: unwrap values so we don't compare logical integers
      // with bounded integers. kill this once we bake the bounded integers.
      case List(i, j) => Val.Bool(Val.unwrap(i) == Val.unwrap(j))
      case _ =>
        throw new EvalException(this, args, "")
