package lack.meta.core.sort

import lack.meta.base.pretty
import lack.meta.base.num.{Integer, Range}

trait Sort extends pretty.Pretty

// TODO: split into representation types with logical sorts,
// eg representation UInt32 has logical sort Integer.
object Sort:
  case object Bool extends Sort:
    def ppr = pretty.text("Bool")

  abstract class Numeric extends Sort

  /** Fixed-width integers with integer arithmetic.
    * Arithmetic overflow is not defined. */
  abstract class Integral(val width: Int, val signed: Boolean) extends Numeric:
    def ppr = pretty.text(if (signed) "Int" else "UInt") <> pretty.value(width)
    def minInclusive: Integer = if (signed) (Integer(-1) << (width - 1)) else 0
    def maxInclusive: Integer = (if (signed) (Integer(1) << (width - 1)) else (Integer(1) << width)) - 1

  // TODO: we probably do want an arbitrary-precision Integer Sort, so we can
  // translate fixed-width integers with proof obligations.
  // This unbounded Integer sort should perhaps not be exposed in source,
  // and C compilation should die if the program uses it other than in proof obligations.

  case object Int8   extends Integral(8, true)
  case object UInt8  extends Integral(8, false)
  case object Int16  extends Integral(16, true)
  case object UInt16 extends Integral(16, false)
  case object Int32  extends Integral(32, true)
  case object UInt32 extends Integral(32, false)
  case object Int64  extends Integral(64, true)
  case object UInt64 extends Integral(64, false)

  /** Integer interval with statically known lower and upper bounds.
    * The "carrier" or representation type dictates how values are stored.
    * Computations are performed on the carrier type.
    * Overflow */
  case class Subrange(minInclusive: Integer, maxInclusive: Integer, carrier: Integral) extends Numeric:
    require(carrier.minInclusive <= minInclusive)
    require(maxInclusive <= carrier.maxInclusive)
    def ppr = carrier.ppr <> pretty.text(s"[${minInclusive}, ${maxInclusive}]")

  /** Syntactic helper for subranges. Uses the smallest carrier set that
    * will fit the entire range, favouring unsigned integers over signed. */
  def subrange(range: Range) =
    val fits = Table.ints.filter(i => i.minInclusive <= range.min && range.max <= i.maxInclusive)
    Subrange(range.min, range.max, fits.headOption.getOrElse(Int64))

  /** A mathematical real number that is represented by 32-bit floats at runtime.
   * This type is cheating a bit. */
  case object Real32 extends Numeric:
    def ppr = pretty.text("Real32")

  object Table:
    val ints =
      List(UInt8, Int8, UInt16, Int16, UInt32, Int32, UInt64, Int64)

    val numeric =
      Real32 :: ints

    /** All base sorts: primitive sorts excluding parametric or compound types
     * such as structs. */
    val base =
      Bool :: numeric

