package lack.meta.base

import scala.collection.immutable.{SortedMap, SortedSet}
import math.Ordering.Implicits.seqOrdering

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

    val INIT      = fromInternal("init")
    val PRE       = fromInternal("pre")
    val FBY       = fromInternal("fby")
    val LOCAL     = fromStringUnsafe("")

  given Ordering_ComponentSymbol: scala.math.Ordering[ComponentSymbol] with
    def compare(x: ComponentSymbol, y: ComponentSymbol): Int =
      x.compareTo(y)

  /** A name component, which can be used as a variable binding. */
  case class Component(symbol: ComponentSymbol, ix: Option[Int]) extends pretty.Pretty:
    def ppr: pretty.Doc =
      pretty.string(symbol + (if (ix.isDefined) s"?${ix.get}" else ""))

  given Ordering_Component: scala.math.Ordering[Component] with
    def compare(x: Component, y: Component): Int =
      summon[Ordering[(ComponentSymbol, Option[Int])]].compare((x.symbol, x.ix), (y.symbol, y.ix))

  /** A reference to a named variable.
   * This may have a path of node instances, to refer to the results of subnodes.
   * We want to be able to refer to multiple levels deep because some invariants
   * might need to dig into the guts of another node.
   * For the generated C code, the path will be used to look in the results of the
   * result struct, but the path is more like a qualified name than a value-level
   * struct access.
   */
  case class Ref(prefix: List[Component], name: Component) extends pretty.Pretty:
    def fullyQualifiedPath: List[Component] = prefix :+ name
    def ppr: pretty.Doc =
      val docs = fullyQualifiedPath.map(_.ppr)
      pretty.ssep(docs, pretty.dot)

  object Ref:
    def fromPathUnsafe(path: List[Component]): Ref =
      require(path.nonEmpty, "fromPathUnsafe: requires non-empty path for variable reference")
      Ref(path.dropRight(1), path.last)

  given Ordering_Ref: scala.math.Ordering[Ref] with
    def compare(x: Ref, y: Ref): Int =
      summon[Ordering[(List[Component])]].compare(x.fullyQualifiedPath, y.fullyQualifiedPath)

  /** A prefix of a qualified path which can be used to qualify names */
  case class Prefix(prefix: List[Component]) extends pretty.Pretty:
    def apply(name: names.Ref): names.Ref =
      names.Ref(prefix ++ name.prefix, name.name)

    def ppr: pretty.Doc =
      val docs = prefix.map(_.ppr)
      pretty.ssep(docs, pretty.dot)

  given Ordering_Prefix: scala.math.Ordering[Prefix] with
    def compare(x: Prefix, y: Prefix): Int =
      summon[Ordering[(List[Component])]].compare(x.prefix, y.prefix)

  /** A hierarchical namespace associating values with some annotation V.
   * This is equivalent to a Map[names.Ref, V].
   */
  case class Namespace[V <: pretty.Pretty](
    values: SortedMap[names.Component, V] = SortedMap(),
    namespaces: SortedMap[names.Component, Namespace[V]] = SortedMap())
    extends pretty.Pretty:
      def <>(that: Namespace[V]): Namespace[V] =
        val values = that.values.foldLeft(this.values) { case (m,v) =>
          this.values.get(v._1).foreach { u =>
            assert(u == v._2, s"Namespace invariant failure, different sorts ${u.pprString} /= ${v._2.pprString} for component ${v._1}")
          }
          m + v
        }
        val namespaces = that.namespaces.foldLeft(this.namespaces) { case (m,n) =>
          m.get(n._1) match {
            case None => m + n
            case Some(nn) => m + (n._1 -> (nn <> n._2))
          }
        }
        Namespace(values, namespaces)
      def ppr =
        val vs = values.map { (k,v) => k.ppr <> pretty.colon <+> v.ppr }
        val ns = namespaces.map { (k,v) => k.ppr <> pretty.colon <+> v.ppr }
        val vns = pretty.ssep((vs ++ ns).toSeq, pretty.semi <> pretty.space)
        pretty.braces(pretty.space <> vns <> pretty.space)

      def refs(prefix: Prefix): Iterable[names.Ref] =
        values.map(v => names.Ref(prefix.prefix, v._1)) ++
        namespaces.flatMap(ns => ns._2.refs(Prefix(prefix.prefix :+ ns._1)))

  object Namespace:
    def fromRef[V <: pretty.Pretty](ref: names.Ref, value: V): Namespace[V] =
      ref.prefix match {
        case Nil =>
          Namespace(values = SortedMap(ref.name -> value))
        case p :: rest =>
          Namespace(namespaces = SortedMap(p -> fromRef(names.Ref(rest, ref.name), value)))
      }
    def nest[V <: pretty.Pretty](name: names.Component, value: Namespace[V]): Namespace[V] =
      Namespace(namespaces = SortedMap(name -> value))

  object immutable:
    type RefMap[V] = scala.collection.immutable.SortedMap[names.Ref, V]
    type RefSet    = scala.collection.immutable.SortedSet[names.Ref]

  object mutable:
    type RefMap[V] = scala.collection.mutable.SortedMap[names.Ref, V]
    type RefSet    = scala.collection.mutable.SortedSet[names.Ref]

    /** Node-level context with a fresh name supply */
    class Supply(val path: List[names.Component]):
      var ixes: scala.collection.mutable.Map[names.ComponentSymbol, Int] =
        scala.collection.mutable.Map().withDefaultValue(0)

      def freshRef(name: names.ComponentSymbol, forceIndex: Boolean = false): names.Ref =
        val ix = ixes(name)
        val ixy = if (ix > 0 || forceIndex) Some(ix) else None
        ixes(name) += 1
        names.Ref(path, names.Component(name, ixy))

      def freshInit(): names.Ref =
        freshRef(names.ComponentSymbol.INIT, forceIndex = true)
