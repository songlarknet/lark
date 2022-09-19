package lack.meta

import lack.meta.base.pretty
import scala.quoted.*

object macros:
  case class Location(enclosing: Option[String], position: Option[Position]) extends pretty.Pretty:
    def ppr = ppr(pretty.emptyDoc)
    def ppr(prefix: pretty.Doc) =
      val txt = position.fold("")(p => s"at ${p.name}:${p.line}:${p.column}") +
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

  case class Position(name: String, line: Int, column: Int)

  inline given location: Location = ${hereImpl}

  given ToExpr_Location: ToExpr[Location] with
    def apply(loc: Location)(using Quotes): Expr[Location] =
      '{Location(${Expr(loc.enclosing)}, ${Expr(loc.position)})}

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
          Some(macros.Position(p.sourceFile.name, p.startLine + 1, p.startColumn))

    def parents(sym: Symbol): List[Symbol] =
      if (sym.maybeOwner == Symbol.noSymbol) Nil else (sym :: parents(sym.maybeOwner))

    val owners = parents(owner).filter { o =>
      (o.isValDef || o.isDefDef) && !o.isLocalDummy
    }

    val encls =
      owners.map(_.name).headOption

    Expr(Location(encls, pos(owner)))
