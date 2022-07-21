package lack.meta

/** */
object base:
  /** TODO: this should be a BigInt.
   * We need >64 bits to represent the full range of signed and unsigned int64s.
   */
  type Integer = scala.Long
  case class Range(min: Integer, max: Integer)