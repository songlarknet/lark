package lack.meta.base

import org.bitbucket.inkytonik.kiama

object pretty extends kiama.output.PrettyPrinter:

  override val defaultIndent: Int = 2
  // override val defaultWidth: Int = 120

  trait Pretty:
    def ppr: Doc

    def pprString: String =
      layout(ppr)

  def csep(l : Seq[Doc]) : Doc =
      ssep(l, comma <> space)

  def tuple(l : Seq[Doc]) : Doc =
      parens(group(nest(csep(l))))

  def tupleP[T <: Pretty](l : Seq[T]) : Doc =
      tuple(l.map(_.ppr))

  def sexpr(l : Seq[Doc]) : Doc =
      parens(group(nest(hsep(l))))

  def subgroup(head: Doc, items : Seq[Doc]) : Doc =
    if (items.nonEmpty)
      nest(head <@> vsep(items)) <> line
    else
      emptyDoc

  // /** TODO: use a pretty-printer library */
  // def indent(head: String, xs: List[String]): String = xs match
  //   case List() => ""
  //   case _ :: _ =>
  //     val xss = xs.flatMap(x => x.split("\n"))
  //     s"  $head\n" + xss.map(x => s"    $x").mkString("\n")

  // def indent(xs: List[String]): String = xs match
  //   case List() => ""
  //   case _ :: _ =>
  //     val xss = xs.flatMap(x => x.split("\n"))
  //     xss.map(x => s"    $x").mkString("\n")
