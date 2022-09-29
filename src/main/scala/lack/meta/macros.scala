package lack.meta

import lack.meta.base.pretty
import scala.quoted.*

/** Macros for getting source information.
 * We want the source position and, as much as possible, the names of the
 * enclosing variables. This information lets the core language names match
 * the source names.
 * I've had trouble getting source position using the macros alone: maybe it
 * doesn't like it in constructors or something. If the macro doesn't work,
 * then we generate an exception and use its stack trace. This is probably not
 * suitable for a "real time" system (!).
 */
object macros:
  case class Location(enclosing: Option[String], position: Option[Position]) extends pretty.Pretty:
    def ppr = ppr(pretty.emptyDoc)
    def ppr(prefix: pretty.Doc) =
      val txt = position.fold("")(p => s"at ${p.name}:${p.line}${p.column.fold("")(":" + _.toString)}") +
                enclosing.fold("")(c => s" in ${c}")
      if txt.nonEmpty
      then prefix <> pretty.text(txt.stripLeading())
      else pretty.emptyDoc
    def prettyPath: String = enclosing.getOrElse("")

    def <>(that: Location): Location = Location(
      enclosing = this.enclosing.orElse(that.enclosing),
      position = this.position.orElse(that.position))

  object Location:
    def empty = Location(None, None)

  case class Position(name: String, line: Int, column: Option[Int])
  object Position:
    def fromException(e: Exception): Option[Position] =
      val sts = e.getStackTrace()
      if sts.length > 0
      then Some(Position(sts(0).getFileName(), sts(0).getLineNumber(), None))
      else None

  inline given location: Location = ${hereImpl}

  given ToExpr_Position: ToExpr[Position] with
    def apply(pos: Position)(using Quotes): Expr[Position] =
      '{Position(${Expr(pos.name)}, ${Expr(pos.line)}, ${Expr(pos.column)})}

  def hereImpl(using Quotes): Expr[Location] =
    import quotes.reflect.*
    val owner = Symbol.spliceOwner.owner
    def pos(sym: Symbol): Option[macros.Position] = sym.pos match
      case None    => None
      case Some(p) =>
        // XXX assertion failure when request startLine.
        // we don't always get good source positions
        if (p.sourceFile.toString() == "<no file>")
          None
        else
          Some(macros.Position(p.sourceFile.name, p.startLine + 1, Some(p.startColumn)))

    def parents(sym: Symbol): List[Symbol] =
      if (sym.maybeOwner == Symbol.noSymbol) Nil else (sym :: parents(sym.maybeOwner))

    val owners = parents(owner).filter { o =>
      (o.isValDef || o.isDefDef) && !o.isLocalDummy
    }

    val encls =
      owners.map(_.name).headOption

    pos(owner) match
      case Some(p) =>
        '{Location(${Expr(encls)}, ${Expr(Some(p))})}
      case None =>
        '{Location(${Expr(encls)}, _root_.lack.meta.macros.Position.fromException(new Exception()))}

