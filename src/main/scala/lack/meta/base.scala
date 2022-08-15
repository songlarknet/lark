package lack.meta

/** Standard stuff for the metalanguage. */
object base:
  /** Use arbitrary-sized integers by default.
   * We need >64 bits to represent the full range of signed and unsigned int64s.
   */
  type Integer = BigInt
  object Integer:
    def apply(i: Int): Integer = BigInt(i)

  case class Range(min: Integer, max: Integer):
    def contains(i: Integer) = min <= i && i <= max


  /** TODO: use a pretty-printer library */
  def indent(head: String, xs: List[String]): String = xs match
    case List() => ""
    case _ :: _ =>
      val xss = xs.flatMap(x => x.split("\n"))
      s"  $head\n" + xss.map(x => s"    $x").mkString("\n")

  def indent(xs: List[String]): String = xs match
    case List() => ""
    case _ :: _ =>
      val xss = xs.flatMap(x => x.split("\n"))
      xss.map(x => s"    $x").mkString("\n")
