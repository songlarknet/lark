package lack.meta.core

import lack.meta.base.Integer
import lack.meta.core.sort.Sort

object term:

  sealed trait Val:
    def pretty: String
    def check(sort: Sort): Boolean

  object Val:
    case class Bool(b: Boolean) extends Val:
      def pretty: String = if (b) "#b'true" else "#b'false"
      def check(sort: Sort) = sort == Sort.Bool

    case class Int(i: Integer) extends Val:
      def pretty: String = s"#int'$i"
      def check(sort: Sort) = sort match
        case sort: Sort.Integral =>
          sort.minInclusive <= i && i <= sort.maxInclusive
        case Sort.Subrange(min, max, _) =>
          min <= i && i <= max
        case _ =>
          false

    case class Mod(i: Integer, width: Sort.Mod) extends Val:
      def pretty: String = s"#mod${width.width}'$i"
      def check(sort: Sort) = sort match
        case m: Sort.Mod =>
          m.range.contains(i) && m.width == width.width
        case _ =>
          false

    case class Float32(r: Float) extends Val:
      def pretty: String = s"#f32'$r"
      def check(sort: Sort) = sort == Sort.Float32

    case class Struct(fields: List[(String, Val)], struct: Sort.Struct) extends Val:
      require(fields.map(_._1) == struct.fields.map(_._1))
      require(struct.fields.zip(fields).forall(f => f._2._2.check(f._1._2)))
      def pretty: String = s"(#${struct.pretty} ${fields.map(f => s":${f._1} ${f._2}").mkString(" ")})"
      def check(sort: Sort) = sort == struct

  /** Pure total primitives. */
  trait Prim:
    def pretty: String
    // def sort(args: List[Sort]): Sort
    def eval(args: List[Val]): Val
  object Prim:

    abstract class Simple(prim: String, expect: List[Sort], ret: Sort) extends Prim:
      def pretty: String = prim

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
      def pretty: String = "ite"
      def eval(args: List[Val]): Val = args match
        case List(Val.Bool(p), t, f) => if (p) t else f

    case object Negate extends Prim:
      def pretty: String = "negate"
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
      def pretty: String = "+"
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ + _))

    case object Sub extends Prim:
      def pretty: String = "-"
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ - _))

    case object Mul extends Prim:
      def pretty: String = "*"
      def eval(args: List[Val]): Val = eval_ii_i(args)((_ * _))

    /** "Safe" division where x / 0 = 0, which agrees with Isabelle and Z3 semantics
     * for integers. However, SMTLib's bitvector semantics for division are that bvudiv
     * returns a bitvector with all ones. For signed division with bvsdiv, the result
     * is -1 or 1 depending on the sign of the left-hand-side.
     * We probably want to wrap bv.div to keep the x/0=0 semantics.
     * TODO: wrap bitvector division in smt encoding
     */
    case object Div extends Prim:
      def pretty: String = "-"
      def eval(args: List[Val]): Val = eval_ii_i(args) {
        case (i, j) => if (j == 0) 0 else (i / j)
      }

    case object Eq extends Prim:
      def pretty: String = "="
      def eval(args: List[Val]): Val = args match
        case List(i, j) => Val.Bool(i == j)

    case object Le extends Prim:
      def pretty: String = "<="
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ <= _))

    case object Lt extends Prim:
      def pretty: String = "<"
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ < _))

    case object Ge extends Prim:
      def pretty: String = ">="
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ >= _))

    case object Gt extends Prim:
      def pretty: String = ">"
      def eval(args: List[Val]): Val = eval_ii_b(args)((_ > _))

    case class StructGet(field: String, struct: Sort.Struct) extends Prim:
      require(struct.fields.map(_._1).contains(field))

      def pretty: String = s"${struct.pretty}'${field}"
      def eval(args: List[Val]): Val = args match
        case List(vstr: Val.Struct) =>
          require(vstr.struct == struct)
          vstr.fields.filter(v => v._1 == field).head._2

    case class StructMk(struct: Sort.Struct) extends Prim:
      def pretty: String = s"${struct.pretty}"
      def eval(args: List[Val]): Val =
        Val.Struct(struct.fields.map(_._1).zip(args).toList, struct)

  sealed trait Exp:
    def pretty: String

  object Exp:
    /** Variable */
    case class Var(v: names.Ref, sort: Sort) extends Exp:
      def pretty: String = s"(as ${v.pretty} ${sort.pretty})"

    /** Value */
    case class Val(v: term.Val) extends Exp:
      def pretty: String = v.pretty

    /** Pure primitive application */
    case class App(prim: term.Prim, args: Exp*) extends Exp:
      def pretty: String = s"(${prim.pretty} ${args.map(_.pretty).mkString(" ")})"

    /** Streaming terms */
    object flow:
      /** Previous value */
      case class Pre(e: Exp) extends Exp:
        def pretty: String = s"(flow'pre ${e.pretty})"
      /** x -> y, or "first x then y". */
      case class Arrow(a: Exp, b: Exp) extends Exp:
        def pretty: String = s"(flow'-> ${a.pretty} ${b.pretty})"

    /** Non-deterministic terms */
    object nondet:
      case class Undefined(s: Sort) extends Exp:
        def pretty: String = s"(undefined ${s.pretty})"
