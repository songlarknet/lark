package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Pure expressions */
sealed trait Exp extends pretty.Pretty:
  // Annotate each node with its type. Is this overkill? The expressions probably won't be "too big"...
  def sort: Sort

object Exp:
  /** Variable */
  case class Var(sort: Sort, v: names.Ref) extends Exp:
    def ppr = v.ppr

  /** Value */
  case class Val(sort: Sort, v: lack.meta.core.term.Val) extends Exp:
    def ppr = v.ppr

  /** Pure primitive application */
  case class App(sort: Sort, prim: Prim, args: Exp*) extends Exp:
    // TODO: should constructors do typechecking?
    def ppr = pretty.sexpr((prim :: args.toList).map(_.ppr))

  /** A cast between two variables with different representation types but the
   * same logical type, eg UInt8 -> UInt32. */
  case class Cast(sort: Sort, e: Exp) extends Exp:
    // TODO move to typechecker
    require(Sort.logical(sort) == Sort.logical(e.sort),
      s"Cannot cast from sort ${e.sort.pprString} to sort ${sort.pprString}")

    def ppr = pretty.sexpr(List(pretty.text("#cast"), sort.ppr, e.ppr))
