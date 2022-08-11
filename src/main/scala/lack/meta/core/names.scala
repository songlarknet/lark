package lack.meta.core

import lack.meta.core.sort.Sort

object names:
  /** Sanitized symbols.
   * These are ensured to be valid SMT-lib identifiers with some extra restrictions.
   *
   * Component symbols allow special characters to be ~, !, @, $, %, ^, &, *, -, +, <, >, /, and _.
   * These are the symbols allowed by SMT-lib except with '?' and '.' removed.
   * Scala symbols allow special characters to be $ and _.
   */
  opaque type ComponentSymbol = String

  object ComponentSymbol:
    /** Make an identifier from given Scala identifier. */
    def fromScalaSymbol(s: String): ComponentSymbol = {
      // TODO: check no bad characters, disallow ^ and ? and .
      require(!s.contains("."), s)
      require(!s.contains("^"), s)
      require(!s.contains("?"), s)
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
    val EMPTY = fromInternal("")

  /** A name component, which can be used as a variable binding. */
  case class Component(symbol: ComponentSymbol, ix: Int):
    def pretty: String = symbol + (if (ix != 0) s"?${ix}" else "")

  /** A reference to a named variable.
   * This may have a path of node instances, to refer to the results of subnodes.
   * We want to be able to refer to multiple levels deep because some invariants
   * might need to dig into the guts of another node.
   * For the generated C code, the path will be used to look in the results of the
   * result struct.
   *
   * The path here is more like a qualified name than a value-level struct access.
   */
  case class Ref(path: List[Component], name: Component):
    def pretty: String = (path :+ name).map(_.pretty).mkString(".")
