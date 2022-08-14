package lack.meta

import scala.quoted.*

object macros:
  case class Location(enclosing: List[String], position: Position):
    def prettyPath: String = enclosing.lastOption.getOrElse("")

  case class Position(name: String, path: String, line: Int, column: Int)

  inline given location: Location = ${hereImpl}

  given ToExpr_Location: ToExpr[Location] with
    def apply(loc: Location)(using Quotes): Expr[Location] =
      '{Location(${Expr(loc.enclosing)}, ${Expr(loc.position)})}

  given ToExpr_Position: ToExpr[Position] with
    def apply(pos: Position)(using Quotes): Expr[Position] =
      '{Position(${Expr(pos.name)}, ${Expr(pos.path)}, ${Expr(pos.line)}, ${Expr(pos.column)})}

  def hereImpl(using Quotes): Expr[Location] =
    import quotes.reflect.*
    val owner = Symbol.spliceOwner.owner
    val pos = owner.pos match
      case None    => macros.Position("", "", 0, 0)
      case Some(p) => macros.Position(p.sourceFile.name, p.sourceFile.path, p.startLine, p.startColumn)

    def parents(sym: Symbol): List[Symbol] =
      if (sym.maybeOwner == Symbol.noSymbol) Nil else (sym :: parents(sym.maybeOwner))

    val owners = parents(owner).filter { o =>
      o.isValDef || o.isDefDef || o.isClassDef || o.isTypeDef
    }

    val encls =
      owners.map(_.name)

    Expr(Location(encls.reverse, pos))
