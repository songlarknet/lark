package lack.meta.base

/** Standard stuff for the metalanguage. */
object num:
  /** Use arbitrary-sized integers by default.
   * We need >64 bits to represent the full range of signed and unsigned int64s.
   */
  type Integer = BigInt
  object Integer:
    def apply(i: Int): Integer = BigInt(i)

  case class Range(min: Integer, max: Integer):
    def contains(i: Integer) = min <= i && i <= max

  /** Represent real numbers as 128-bit floating decimal-point by default.
   * 128-bit should be sufficient since the runtime representation will be at
   * most 64-bit floats, but perhaps this should be a pair of BigInts.
   */
  type Real = BigDecimal

  object Real:
    def apply(i: BigInt): Real = BigDecimal(i)
    def decimal(d: Double): Real = BigDecimal.decimal(d)
