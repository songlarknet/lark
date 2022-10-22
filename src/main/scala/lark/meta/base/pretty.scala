package lark.meta.base

import org.bitbucket.inkytonik.kiama

object pretty extends kiama.output.PrettyPrinter:

  override val defaultIndent: Int = 2
  override val defaultWidth: Int = 120

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

  /** Assignment syntax */
  val gets = colon <> equal

  object Colour:
    def escape(code: Code): Doc =
      text("\u001b[" + code.string + "m")

    case class Code(string: String):
      def ppr = escape(this)
      def of(doc: Doc): Doc =
        escape(this) <> doc <> escape(Reset)

    object Red extends Code("31")
    object Green extends Code("32")
    object Yellow extends Code("33")
    object Grey extends Code("90")
    object Reset extends Code("")
