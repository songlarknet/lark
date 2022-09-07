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
