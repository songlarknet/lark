package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Logical representation of values */
sealed trait Val extends pretty.Pretty:
  def sort: Sort

object Val:
  /** Boolean values. */
  case class Bool(b: Boolean) extends Val:
    def ppr = pretty.text(if (b) "#b'true" else "#b'false")
    def sort = Sort.Bool

  /** Unbounded integer values.
   *
   * Operations on these use unbounded arithmetic, at least conceptually,
   * but to compile these operations we need to prove that they don't
   * overflow the runtime representation type. */
  case class Int(i: Integer) extends Val:
    def ppr = pretty.text(s"#int'$i")
    def sort = Sort.ArbitraryInteger

  /** Mathematical real number.
   *
   * These values are logically reals, but the compiled runtime
   * representation is a float, which is a bit of a lie. */
  case class Real(r: num.Real) extends Val:
    def ppr = pretty.string(s"#r'$r")
    def sort = Sort.Real

  /** Check if a value matches a sort.
   *
   * Bounded integers are fake refinement types, so that the value Val.Int(0)
   * fits type UInt8, Int32, and so on. */
  def check(v: Val, sort: Sort): Boolean = sort match
    case r: Sort.Refinement =>
      check(v, r.logical) && r.refinesVal(v)
    case _ =>
      v.sort == sort
