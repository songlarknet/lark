package lack.meta.core

import lack.meta.core.sort.Sort

object names:
  /** Sanitized symbols.
   * These are ensured to be valid SMT-lib identifiers with some extra restrictions.
   *
   * Component symbols allow special characters to be ~, !, @, $, %, ^, &, *, -, +, <, >, /, and _.
   * These are the symbols allowed by SMT-lib except SMT-lib also allows '?' and '.' and doesn't
   * support unicode.
   * Scala symbols allow special characters to be $ and _.
   */
  opaque type ComponentSymbol = String

  object ComponentSymbol:
    /** Make an identifier from given Scala identifier. */
    def fromScalaSymbol(s: String): ComponentSymbol = {
      // TODO: check no bad characters, disallow ^ and ? and .
      // TODO: what about unicode?
      require(!s.contains("."), s"Illegal character: '$s' should not contain '.'")
      require(!s.contains("^"), s"Illegal character: '$s' should not contain '^'")
      require(!s.contains("?"), s"Illegal character: '$s' should not contain '?'")
      s
    }
    /** Make an internal component name.
     * These won't clash with names that come from Scala identifiers.
     */
    def fromInternal(s: String): ComponentSymbol = "^" + fromScalaSymbol(s)

    /** Trust me. */
    def fromStringUnsafe(s: String): ComponentSymbol = s
    def pretty(c: ComponentSymbol): String = c

    val INIT  = fromInternal("init")
    val LOCAL = fromStringUnsafe("")

  /** A name component, which can be used as a variable binding. */
  case class Component(symbol: ComponentSymbol, ix: Option[Int]):
    def pretty: String = symbol + (if (ix.isDefined) s"?${ix.get}" else "")

  /** A reference to a named variable.
   * This may have a path of node instances, to refer to the results of subnodes.
   * We want to be able to refer to multiple levels deep because some invariants
   * might need to dig into the guts of another node.
   * For the generated C code, the path will be used to look in the results of the
   * result struct, but the path is more like a qualified name than a value-level
   * struct access.
   */
  case class Ref(prefix: List[Component], name: Component):
    def fullyQualifiedPath: List[Component] = prefix :+ name
    def pretty: String = fullyQualifiedPath.map(_.pretty).mkString(".")

  object Ref:
    def fromPathUnsafe(path: List[Component]): Ref =
      require(path.nonEmpty, "fromPathUnsafe: requires non-empty path")
      Ref(path.dropRight(1), path.last)
