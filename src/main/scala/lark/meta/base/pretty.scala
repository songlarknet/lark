package lark.meta.base

import org.bitbucket.inkytonik.kiama
import kiama.output.PrettyPrinterTypes.{Width, Link, LinkValue}

object pretty extends kiama.output.PrettyPrinter:

  override val defaultIndent: Int = 2
  override val defaultWidth: Int = 120

  trait Pretty:
    def ppr: Doc

    def pprString: String =
      layout(ppr)

  override def layout(d: Doc, w: Width = defaultWidth) : String =
    colour(d, w)

  def mono(d: Doc, w: Width = defaultWidth) : String =
    pretty(d, w).layout

  def colour(d: Doc, w: Width = defaultWidth) : String =
    val ppr = pretty(d, w)
    val builder = new StringBuilder(ppr.layout.size)

    def build(rendered: String, links: List[(Range, Colour.Code)], stack: List[(Int, Colour.Code)], pos: Int, current: Colour.Code): Unit =
      (links, stack) match
        case (Nil, Nil) =>
          builder ++= rendered
        case (Nil, (end,code) :: rstack) =>
          val (prefix,rdoc) = rendered.splitAt(end - pos)
          builder ++= prefix
          builder ++= Colour.escape(code)
          build(rdoc, links, rstack, end, code)
        case ((range, code) :: rlinks, Nil) =>
          val (prefix,rdoc) = rendered.splitAt(range.start - pos)
          builder ++= prefix
          builder ++= Colour.escape(code)
          build(rdoc, rlinks, (range.end, current) :: stack, range.start, code)
        case ((range, code) :: rlinks, (end,scode) :: rstack) =>
          if end < range.end
          then
            val (prefix,rdoc) = rendered.splitAt(end - pos)
            builder ++= prefix
            builder ++= Colour.escape(scode)
            build(rdoc, links, rstack, end, scode)
          else
            val (prefix,rdoc) = rendered.splitAt(range.start - pos)
            builder ++= prefix
            builder ++= Colour.escape(code)
            build(rdoc, rlinks, (range.end, current) :: stack, range.start, code)

    val sorted = ppr.links.flatMap {
      case LinkValue(code: Colour.Code, range) => Some((range, code))
      case _ => None
    }.sortBy(_._1.start)
    build(ppr.layout, sorted, List(), 0, Colour.Reset)
    builder.result

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

  /** Nest expression, inserting parentheses if precedence of enclosing
   * operator is lower than or equal to the precedence of inner operator.
   */
  def precedence(enclosing: Int, inner: Int, doc: Doc) =
    if enclosing < inner
    then parens(doc)
    else doc

  /** Assignment syntax */
  val gets = colon <> equal

  object Colour:
    def escape(code: Code): String =
      "\u001b[" + code.string + "m"

    case class Code(string: String):
      def ppr = escape(this)
      def of(doc: Doc): Doc =
        link(this, doc)

    object Red extends Code("31")
    object Green extends Code("32")
    object Yellow extends Code("33")
    object Grey extends Code("90")
    object Reset extends Code("")
