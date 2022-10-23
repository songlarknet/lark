package lark.meta.core.node.transform

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.collection.{Graph, MultiMap}

import scala.collection.{mutable, immutable}
import lark.meta.core.node.{Node, Variable, Schedule}
import lark.meta.core.node.Node.Binding
import lark.meta.core.term.{Exp, Flow}
import lark.meta.core.term.Compound

object InlineBindings:
  /** Inline the local bindings in nodes. */
  def program(nodes: Iterable[Node]): Iterable[Node] =
    val map = scala.collection.mutable.SortedMap[names.Ref, Node]()
    nodes.map { n =>
      val t = node(n, map)
      map += (n.klass -> t)
      t
    }

  /** Inline the local bindings in a node. */
  def node(n: Node, nodes: names.mutable.RefMap[Node]): Node =
    val blacklist =
      n.props.flatMap { p =>
        lark.meta.core.term.Compound.take.vars(p.term).map(_.v.name)
      } ++
      n.vars.filter { (c,v) =>
        v.mode != Variable.Generated
      }.map(_._1)

    val graph =
      Schedule.Slurp(n, includePreDependencies = true).graph().reverse

    val t = perform(n, plan(n.nested, graph, immutable.SortedSet.from(blacklist)))
    t.copy(subnodes = t.subnodes.map { (k,v) =>
      k -> nodes(v.klass)
    })

  case class Plan(
    subst:  names.immutable.RefMap[Exp]):
    def <>(that: Plan): Plan =
      // We need to merge the two substitutions, but one side may refer to
      // variables mentioned in the other. Substitute both into each other.
      val subst =
        this.subst.mapValues(Compound.subst(that.subst, _)) ++
        that.subst.mapValues(Compound.subst(this.subst, _))
      Plan(immutable.SortedMap.from(subst))

  object Plan:
    def empty = Plan(immutable.SortedMap())

  def plan(n: Node.Nested, graph: Graph[Schedule.Entry], blacklist: names.immutable.ComponentSet): Plan =
    val plans = n.children.map { c =>
      plan(c, graph, blacklist)
    }
    plans.fold(Plan.empty)(_ <> _)

  def plan(b: Node.Binding, graph: Graph[Schedule.Entry], blacklist: names.immutable.ComponentSet): Plan =
    b match
      case Binding.Equation(lhs, Flow.Pure(rhs)) =>
        if blacklist.contains(lhs)
        then Plan.empty
        else
          // PERF wrong complexity do a lookup
          // Check that this name is not defined in multiple places.
          // If it's defined in multiple merges then don't inline at all, because
          // the actual value depends on which merge is activated.
          val entries = graph.vertices.filter { e => e.name == lhs && e.kind == Schedule.Entry.Equation }
          val usages  = entries.flatMap { e => graph.edges(e) }
          if entries.size == 1 && usages.size <= 1
          then Plan(
            immutable.SortedMap(names.Ref.fromComponent(lhs) -> rhs))
          else Plan.empty
      case Binding.Equation(lhs, _) =>
        // We can't trivially substitute streaming operations such as pre
        Plan.empty
      case Binding.Subnode(subnode, args) =>
        Plan.empty
      case Binding.Merge(scrutinee, cases) =>
        cases.map { (v,n) =>
          plan(n, graph, blacklist)
        }.fold(Plan.empty)(_ <> _)
      case Binding.Reset(clock, nested) =>
        plan(nested, graph, blacklist)

  def perform(n: Node, plan: Plan): Node =
    val subst    = plan.subst
    val vars     = n.vars.filter { (k,v) => !subst.contains(n.xvar(k).v) }
    val subnodes = n.subnodes
    val props    = n.props.map { p =>
      p.copy(term = Compound.subst(subst, p.term))
    }
    val nested   = perform(n, n.nested, plan)
    Node(n.klass, n.metas, n.params, vars, subnodes, props, nested)

  def perform(node: Node, n: Node.Nested, plan: Plan): Node.Nested =
    val children = n.children.flatMap { perform(node, _, plan) }
    Node.Nested(n.context, children)

  def perform(node: Node, b: Node.Binding, plan: Plan): Option[Node.Binding] = b match
    case Binding.Equation(lhs, rhs) =>
      if plan.subst.contains(node.xvar(lhs).v)
      then None
      else Some(Binding.Equation(lhs, Compound.subst(plan.subst, rhs)))
    case Binding.Subnode(subnode, args) =>
      Some(Binding.Subnode(subnode, args.map(Compound.subst(plan.subst, _))))
    case Binding.Merge(scrutinee, cases) =>
      val casesX = cases.map { (v,n) =>
          (v, perform(node, n, plan))
        }
      Some(Binding.Merge(Compound.subst(plan.subst, scrutinee), casesX))
    case Binding.Reset(clock, nested) =>
      val nestedX = perform(node, nested, plan)
      Some(Binding.Reset(Compound.subst(plan.subst, clock), nestedX))

