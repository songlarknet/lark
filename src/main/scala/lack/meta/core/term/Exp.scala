package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.Sort

/** Pure expressions */
sealed trait Exp extends pretty.Pretty:
  // Annotate each node with its type. Is this overkill? The expressions probably won't be "too big"...
  def sort: Sort

object Exp:
  /** Variable */
  case class Var(sort: Sort, v: names.Ref) extends Exp:
    def ppr = v.ppr

  /** Value */
  case class Val(v: lack.meta.core.term.Val) extends Exp:
    def sort = v.sort
    def ppr = v.ppr

  /** Pure primitive application */
  case class App(sort: Sort, prim: Prim, args: Exp*) extends Exp:
    def ppr = pretty.sexpr((prim :: args.toList).map(_.ppr))

  /** A cast between two variables with different representation types but the
   * same logical type, eg UInt8 -> UInt32. */
  case class Cast(op: Cast.Op, e: Exp) extends Exp:
    def sort = op match
      case Cast.Box(r) => r
      case Cast.Unbox(r) => r

    def ppr = pretty.sexpr(List(op.ppr, e.ppr))

  object Cast:
    sealed trait Op extends pretty.Pretty
    case class Box(sort: Sort.Refinement) extends Op:
      def ppr = pretty.text("#box'") <> sort.valuePrefix
    case class Unbox(sort: Sort) extends Op:
      def ppr = pretty.text("#unbox")
