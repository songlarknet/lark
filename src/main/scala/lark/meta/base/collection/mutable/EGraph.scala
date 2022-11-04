package lark.meta.base.collection.mutable

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
 * analyses. We only implement the first (explicit rebuild) here yet.
 *
 * To implement this I also referred to the Python reference implementation at
 *  https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid?usp=sharing
 * and the Rust implementation at https://github.com/egraphs-good/egg.
 */
class EGraph[T]:
  type Node       = EGraph.Node[T]
  type Class      = EGraph.Id
  type ClassUsage = EGraph.ClassUsage[T]

  /** Union-find or "U" in paper that keeps track of the canonical class for
    * each class id. */
  val unionFind = EGraph.UnionFind()

  /** Map from e-class id to e-class usage information. */
  val classes  = mutable.HashMap[Class, ClassUsage]()

  /** Hashcons or "H" in paper to avoid re-creating classes from the same
   * canonical node. */
  val nodes    = mutable.HashMap[Node, Class]()

  /** Worklist of classes that need to be repaired. */
  val worklist = mutable.ArrayBuffer[Class]()

  /** Version, useful for checking if graph is at a fixed point. */
  var version: Long = 0

  /** Add a new node, returning its e-class. */
  def add(node: Node): Class =
    val nodeX = this.canonicalize(node)
    val klass = nodes.getOrElseUpdate(nodeX, {
      this.version += 1

      val klass = this.newSingletonClass(nodeX)
      nodeX.children.foreach { child =>
        classes(child).parents += (nodeX -> klass)
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
      val cu1 = classes(c1)
      val cu2 = classes(c2)
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
    val usage = classes(klass)
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
    classes(this.find(klass)).parents ++= newParents

  /** Construct a fresh equivalence class for a previously-unseen node */
  private def newSingletonClass(node: Node): Class =
    val id    = this.unionFind.allocate()
    val usage = EGraph.ClassUsage[T](id)
    classes += (id -> usage)
    id


object EGraph:
  class ClassUsage[T](val id: Id):
    var parents = mutable.HashMap[Node[T], Id]()

  case class Node[T](val op: T, val children: List[Id])

  case class Id(index: Int)

  class UnionFind:
    val parents = mutable.ArrayBuffer[Id]()

    def allocate(): Id =
      val id = Id(parents.length)
      this.parents += id
      id

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
     * identifiers must both be canonical. The left identifier is the new
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