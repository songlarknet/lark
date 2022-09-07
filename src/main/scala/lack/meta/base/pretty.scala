package lack.meta.base

object pretty:
  // object P extends org.bitbucket.inkytonik.kiama.output.PrettyPrinter

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
