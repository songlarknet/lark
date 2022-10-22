package lark.meta.core.node

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.collection.{Graph, MultiMap}

import scala.collection.immutable
import lark.meta.core.node.Node.Binding.Equation
import lark.meta.core.node.Node.Binding.Subnode
import lark.meta.core.node.Node.Binding.Merge
import lark.meta.core.node.Node.Binding.Reset

object Slice:
  /** Slice nodes so that only the bindings directly relevant to return values
   * and parameters remain. */
  def program(nodes: Iterable[Node]): Iterable[Node] =
    nodes.map(node(_))

  /** Slice a node so that only the bindings directly relevant to return values
   * and parameters remain. */
  def node(n: Node): Node =
    val vars = n.vars.filter { case (k,v) =>
      v.mode == Variable.Argument || v.mode == Variable.Forall || v.mode == Variable.Output
    }
    node(n, vars.keySet)

  def node(n: Node, seed: names.immutable.ComponentSet): Node =
    val graph = Schedule.Slurp(n, includePreDependencies = true).graph()
    val deps = dependencies(graph, seed)
    sliceNode(n, deps)

  def dependencies(g: Graph[Schedule.Entry], seed: names.immutable.ComponentSet): names.immutable.ComponentSet =
    val gx = MultiMap(g.edges.entries.toSeq.map { case (k,v) =>
      k.name -> v.map(_.name).toList
    } : _*)

    def go(acc: names.immutable.ComponentSet, v: names.Component): names.immutable.ComponentSet =
      gx(v).foldLeft(acc + v) { case (accc, vv) =>
        if accc.contains(vv)
        then accc
        else go(accc, vv)
      }

    seed.foldLeft(seed) { case (acc, v) =>
      go(acc, v)
    }

  def sliceNode(n: Node, only: names.immutable.ComponentSet): Node =
    val vars     = n.vars.filter { case (k,v) => only.contains(k) }
    val subnodes = n.subnodes.filter { case (k,v) => only.contains(k) }
    val props    = n.props.filter { p =>
      // All free variables must be mentioned in the keep set.
      // For subnode references "subnode.output" check just "subnode".
      lark.meta.core.term.Compound.take.vars(p.term).forall { v =>
        only.contains(v.v.fullyQualifiedPath.head)
      }
    }
    val nested   = sliceNested(n.nested, only)
    Node(n.klass, n.metas, n.params, vars, subnodes, props, nested)

  def sliceNested(n: Node.Nested, only: names.immutable.ComponentSet): Node.Nested =
    val children = n.children.flatMap { sliceBinding(_, only) }
    Node.Nested(n.context, children)

  def sliceBinding(b: Node.Binding, only: names.immutable.ComponentSet): Option[Node.Binding] =
    b match
      case Equation(lhs, rhs) =>
        if only.contains(lhs) then Some(b) else None
      case Subnode(subnode, args) =>
        if only.contains(subnode) then Some(b) else None
      case Merge(cases) =>
        if cases.exists { case (k,n) => only.contains(n.context) }
        then
          Some(Merge(cases.map { case (k,n) =>
            (k, sliceNested(n, only))
          }))
        else
          None
      case Reset(clock, nested) =>
        if only.contains(nested.context)
        then
          Some(Reset(clock, sliceNested(nested, only)))
        else
          None

