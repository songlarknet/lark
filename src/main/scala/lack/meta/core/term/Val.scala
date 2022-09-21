package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Logical representation of values */
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
