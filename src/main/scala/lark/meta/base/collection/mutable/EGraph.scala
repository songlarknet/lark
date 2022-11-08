package lark.meta.base.collection.mutable

import lark.meta.base.pretty
import scala.collection.mutable

/**
 * Equivalence graphs based on the egg paper:
 *  egg: Fast and extensible equality saturation,
 *  Willsey, Nandi, Wang, Flatt, Tatlock, Panchekha, 2020.
 *  https://arxiv.org/pdf/2004.03082.pdf
 *
 * Equivalence graphs describe equivalences between sets of terms such that
 * the graph is always closed under congruence. You can apply rewrite rules to
 * expand the equivalences and then extract information about which terms are
 * equivalent.
 * The key contributions of the egg paper are splitting out the invariant
 * maintenance to an explicit rebuild step, and adding a framework for e-class
 * analyses. We only implement the first (explicit rebuild) here yet, but the
 * analyses would be useful for constant folding at least.
 *
 * To implement this I also referred to the Python reference implementation at
 *  https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid?usp=sharing
 * I'd recommend reading the paper for an overview, then looking at the Python
 * reference implementation. The reference code in the paper has a few
 * omissions.
 */
class EGraph[T] extends Cloneable with pretty.Pretty:
  type Node       = EGraph.Node[T]
  type Class      = EGraph.Id

  /** Union-find or "U" in paper that keeps track of the canonical class for
    * each class id. */
  val unionFind = EGraph.UnionFind()

  /** Map from e-class id to e-class usage information. */
  val usages    = mutable.SortedMap[Class, EGraph.ClassUsage[T]]()

  /** Hashcons or "H" in paper to avoid re-creating classes from the same
   * canonical node. */
  val nodes     = mutable.HashMap[Node, Class]()

  /** Worklist of classes that need to be repaired. */
  val worklist  = mutable.ArrayBuffer[Class]()

  /** Version, useful for checking if graph is at a fixed point. */
  var version: Long = 0

  /** Add a new node, returning its e-class. */
  def add(node: Node): Class =
    val nodeX = this.canonicalize(node)
    val klass = nodes.getOrElseUpdate(nodeX, {
      this.version += 1

      val klass = this.newSingletonClass(nodeX)
      nodeX.children.foreach { child =>
        usages(child).parents += (nodeX -> klass)
      }
      klass
    })
    // The paper suggests that find is not necessary here, as the `nodes`
    // hashcons maps from node to canonical class, but this invariant is broken
    // by merging.
    this.find(klass)

  /** Helper for adding node operator */
  def add(op: T, children: Class*): Class =
    add(EGraph.Node(op, children.toList))

  /** Merge two equivalence classes together, returning the merged class.
   * This operation does not maintain the congruence relation and instead
   * defers the work to an explicit rebuild step. This behaviour differs from
   * traditional e-graphs.
   * Make sure you call rebuild before querying the e-graph again, or you could
   * get stale values.
   */
  def merge(k1: Class, k2: Class): Class =
    // Find canonical classes c1 and c2.
    val c1 = this.find(k1)
    val c2 = this.find(k2)
    if c1 == c2
    then c1
    else
      this.version += 1
      this.unionFind.unionLeft(c1, c2)
      // We have merged c2 into c1, so any nodes that refer to c2 will need to
      // be normalized to refer to c1. Add any nodes that refer to c2 to c1's
      // parents map so it can find them later, and then add c1 to the worklist
      // to be rebuilt.
      val cu1 = usages(c1)
      val cu2 = usages(c2)
      cu1.parents ++= cu2.parents
      cu2.parents.clear()
      this.worklist += c1
      c1

  /** Canonicalize a node so that all of its arguments (children) refer to
   * canonical class identifiers. */
  def canonicalize(node: Node): Node =
    val children = node.children.map(this.unionFind.find(_))
    EGraph.Node(node.op, children)

  /** Find the canonical class identifier for the given equivalence class. */
  def find(klass: Class): Class =
    this.unionFind.find(klass)

  /** Rebuild the nodes map and the congruence relation after some classes have
   * been merged. */
  def rebuild(): Unit =
    while (this.worklist.nonEmpty)
      // Normalise the worklist so that we only repair each equivalence class
      // once.
      val todo = mutable.HashSet.from(this.worklist.map(this.find(_)))
      // Repairing a class can trigger more work, so clear the worklist first.
      this.worklist.clear()
      todo.foreach { klass =>
        this.repair(klass)
      }

  /** Repair the invariants for the given class. */
  private def repair(klass: Class): Unit =
    val usage = usages(klass)
    // Ensure that the map from canonical nodes to classes points to the
    // canonical class.
    usage.parents.foreach { (pnode, pklass) =>
      this.nodes -= pnode
      val pnodeX = this.canonicalize(pnode)
      this.nodes += (pnodeX -> this.find(pklass))
    }

    // Clear the parents because we're going to re-create them, but keep a copy
    // around so we can loop over them.
    // The merging in the loop can update klass.parents too, so we need to
    // clear it before the loop or we'd lose any updates.
    val parents    = usage.parents
    val newParents = mutable.HashMap[Node, Class]()
    usage.parents  = mutable.HashMap[Node, Class]()

    parents.foreach { (pnode, pklass) =>
      val pnodeX = this.canonicalize(pnode)
      newParents.get(pnodeX) match
        // Two separate parent nodes are now equivalent, so we can merge the
        // two classes together. This will enqueue more work on the worklist.
        case Some(pklassX) =>
          val merged = this.merge(pklass, pklassX)
          newParents += (pnodeX -> merged)
        case None =>
          newParents += (pnodeX -> this.find(pklass))
    }

    // The paper does not have a find here, but the Python reference code does.
    // If a class refers to itself, eg "x = f x", then normalising its parents
    // might merge the class itself.
    usages(this.find(klass)).parents ++= newParents

  /** Get all of the equivalence classes and the terms inside them as nodes */
  def classes: mutable.SortedMap[Class, mutable.HashSet[Node]] =
    val map = mutable.SortedMap[Class, mutable.HashSet[Node]]()
    this.nodes.foreach { (node, klass) =>
      val set = map.getOrElseUpdate(this.find(klass), mutable.HashSet[Node]())
      set.add(node)
    }
    map

  /** Create a distinct mutable copy of this e-graph. */
  override def clone(): EGraph[T] =
    val neu = EGraph[T]()
    neu.unionFind.copyFrom(this.unionFind)
    neu.usages   ++= this.usages
    neu.nodes    ++= this.nodes
    neu.worklist ++= this.worklist
    neu.version    = this.version
    neu


  /** Construct a fresh equivalence class for a previously-unseen node */
  private def newSingletonClass(node: Node): Class =
    val id    = this.unionFind.allocate()
    val usage = EGraph.ClassUsage[T](id)
    usages += (id -> usage)
    id

  def ppr =
    pretty.vsep(classes.map { (c,ns) =>
      val nsP = pretty.ssep(ns.toSeq.map(_.ppr), pretty.comma <> pretty.space)
      c.ppr <+> pretty.text(":=") <+> pretty.braces(pretty.space <> nsP <> pretty.space)
    }.toSeq)

object EGraph:

  /** An equivalence class identifier. */
  case class Id(index: Int) extends pretty.Pretty:
    def ppr = pretty.text("$") <> pretty.value(index)

  given Ordering_Id: scala.math.Ordering[Id] with
    def compare(x: Id, y: Id): Int =
      summon[Ordering[Int]].compare(x.index, y.index)

  /** Nodes represent terms and term applications. The operator `op` can
   * represent a base value or variable, or a primitive or function to be
   * applied. For primitives and functions the `children` list denotes the
   * arguments, which refer to equivalence classes rather than explicit terms.
   * For values and variables the `children` should be empty.
   */
  case class Node[T](val op: T, val children: List[Id]) extends pretty.Pretty:
    def ppr =
      if children.nonEmpty
      then pretty.parens(pretty.hsep(pretty.value(op) :: children.map(_.ppr)))
      else pretty.value(op)

  /** This internal data structure records the occurrences of each equivalence
   * class. The parents map should be empty for non-canonical class
   * identifiers. */
  class ClassUsage[T](val id: Id):
    var parents = mutable.HashMap[Node[T], Id]()

  /** Union-find data structure that tracks equivalence classes. */
  class UnionFind:
    /** The parents array is conceptually a map from Id to the parent Id.
     * For canonical identifiers, the parent is the identifier itself. Two
     * identifiers refer to the same equivalence class if they have shared
     * ancestry.
    */
    val parents = mutable.ArrayBuffer[Id]()

    /** Allocate a new, canonical equivalence class. */
    def allocate(): Id =
      val id = Id(parents.length)
      this.parents += id
      id

    /** Find the canonical identifier for the equivalence class referred to by
     * the given identifier. Two identifiers `a` and `b` refer to the same
     * equivalence class if `find(a) == find(b)`. */
    def find(id: Id): Id =
      var current = id
      while (current != this.parents(current.index))
        val p   = this.parents(current.index)
        val pp  = this.parents(p.index)
        this.parents(current.index)
                = pp
        current = pp
      current

    /** Merge two canonical equivalence classes together. The two input class
     * identifiers must both be canonical. The `left` identifier is the new
     * canonical id.
     *
     * The e-graph relies on this merging into the left.
     *
     * > requires { find(left)  == left }
     * > requires { find(right) == right }
     * > ensures  { find(left)  == find(right) == left }
     * > ensures  { forall i.
     * >     find(i) = if old find(i) == left || old find(i) == right
     * >               then left
     * >               else old find(i) }
     */
    def unionLeft(left: Id, right: Id): Unit =
      this.parents(right.index) = left

    /** Copy the equivalence sets from a new empty UnionFind structure. */
    def copyFrom(old: UnionFind): Unit =
      assert(this.parents.isEmpty, "cannot clone into non-empty UnionFind structure - it would mess up the identifiers")
      this.parents ++= old.parents


  // class Match[T](graph: EGraph[T]):
  //   val classes = graph.classes

  //   object take:
  //     def unop(k: graph.Class): Seq[(T, graph.Class)] =
  //       classes(k).toSeq.flatMap { n =>
  //         if n.children.length == 1
  //         then Some((n.op, n.children.head))
  //         else None
  //       }

  //     def pre(k: graph.Class): Seq[graph.Class] =
  //       unop(k).flatMap { (op,arg) =>
  //         if op == Pre
  //         then Some(arg)
  //         else None
  //       }

  //     def pure(k: graph.Class): Seq[(T, List[graph.Class])] =
  //       classes(k).toSeq.flatMap { n =>
  //         if n.op.isPure
  //         then Some((n.op, n.children))
  //         else None
  //       }

  //   object make:
  //     def pre(p: graph.Class): graph.Class =
  //       graph.add(Op.Pre, p)
  //     def op(op: T, p: graph.Class*): graph.Class =
  //       graph.add(op, p*)

  //   def match1(k: graph.Class): Seq[graph.Class] =
  //     for
  //       arg       <- take.pre(k)
  //       (op,args) <- take.pure(arg)
  //     yield
  //       make.op(op, args.map(make.pre(_))*)

  //   // pre (map f e) = map f (pre e)
  //   // m.take(Pre) match
  //   //   case List(m.node(_ : Map, e)) => e


  //   // e -> e = e
  // object Match
