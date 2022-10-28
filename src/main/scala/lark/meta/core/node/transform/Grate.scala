package lark.meta.core.node.transform

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.collection.{Graph, MultiMap}

import scala.collection.immutable
import lark.meta.core.node.{Node, Variable, Schedule}
import lark.meta.core.node.Node.Binding
import lark.meta.core.node.Node.Binding.Equation
import lark.meta.core.term.Compound

/** Grating is like slicing, but you end up with smaller pieces.
 *
 * Slicing assumes that each subnode is sliced separately with respect to its
 * output values and input parameters. That makes it suitable for separate
 * compilation. For model checking, however, it can be useful to slice each
 * node invocation differently according to how its results are used.
 */
object Grate:
  /** Deeply slice a node so that only the bindings directly relevant to the seed set
   * remain. This transform recurses into the subnodes.
   *
   * NOTE: this transform changes each subnode uniquely, but it does not rename
   * the subnode invocations to have different class name references. This
   * means that the result won't compile cleanly.
   */
  def node(n: Node, seed: names.immutable.RefSet): Node =
    val deps = deepDependencies(names.Prefix(List()), n)
    val only = fixSeed(seed, deps)
    grateNode(names.Prefix(List()), n, only)

  def deepDependencies(prefix: names.Prefix, n: Node) : MultiMap[names.Ref, names.Ref] =
    // The dependency graph is quite coarse with respect to subnode
    // dependencies, so we need to add a bit extra info.
    val graph = Schedule.Slurp(n, includePreDependencies = true).graph()
    val edges0 = MultiMap(graph.edges.entries.toSeq.map { case (k,vs) =>
      prefix(k.name) -> vs.filter(_.kind != Schedule.Entry.Subnode).map(v => prefix(v.name)).toList
    }*)

    def go(nested: Node.Nested): MultiMap[names.Ref, names.Ref] =
      MultiMap.concat(nested.children.map { b =>
        b match
          case Node.Binding.Equation(lhs, rhs) =>
            MultiMap(prefix(lhs) -> Compound.take.vars(rhs).map(v => prefix(v.v)).toList)
          case Node.Binding.Subnode(subnode, args) =>
            val sn = n.subnodes(subnode)
            MultiMap(sn.params.zip(args).map { (p, e) =>
              prefix(names.Ref(List(subnode), p)) ->
                (prefix(nested.context) :: Compound.take.vars(e).map(v => prefix(v.v)).toList)
            }*)
          case Node.Binding.Merge(scrutinee, cases) =>
            val s0 = MultiMap(prefix(nested.context) -> Compound.take.vars(scrutinee).map(v => prefix(v.v)).toList)
            MultiMap.concat(
              s0 :: cases.map((v,n) => go(n))
            )
          case Node.Binding.Reset(clock, nestedX) =>
            val s0 = MultiMap(prefix(nested.context) -> Compound.take.vars(clock).map(v => prefix(v.v)).toList)
            s0 <> go(nestedX)
      })

    val edgesS = go(n.nested)

    val subgraphs = n.subnodes.map((c, sn) => deepDependencies(prefix ++ names.Ref.fromComponent(c), sn))
    MultiMap.concat(Seq(edges0, edgesS) ++ subgraphs)

  def fixSeed(seed: names.immutable.RefSet, deps: MultiMap[names.Ref, names.Ref]): names.immutable.RefSet =
    def go(acc: names.immutable.RefSet, v: names.Ref): names.immutable.RefSet =
      deps(v).foldLeft(acc + v) { case (accc, vv) =>
        if accc.contains(vv)
        then accc
        else go(accc, vv)
      }

    seed.foldLeft(seed) { case (acc, v) =>
      go(acc, v)
    }

  def grateNode(prefix: names.Prefix, n: Node, only: names.immutable.RefSet): Node =
    val params   = n.params.filter { case k => only.contains(prefix(k)) }
    val vars     = n.vars.filter { case (k,v) => only.contains(prefix(k)) }
    val subnodes = n.subnodes.flatMap { case (k,sn) =>
      val prefixX  = prefix(k).fullyQualifiedPath
      val required = only.exists(r => r.prefix.startsWith(prefixX))
      if required
      then Some(k -> grateNode(prefix ++ names.Ref.fromComponent(k), sn, only))
      else None
    }
    val props    = n.props.filter { p =>
      // All free variables must be mentioned in the keep set.
      // For subnode references "subnode.output" check just "subnode".
      lark.meta.core.term.Compound.take.vars(p.term).forall { v =>
        only.contains(v.v)
      }
    }
    val nested   = grateNested(prefix, n, n.nested, only)
    Node(n.klass, n.metas, params, vars, subnodes, props, nested)

  def grateNested(prefix: names.Prefix, node: Node, n: Node.Nested, only: names.immutable.RefSet): Node.Nested =
    val children = n.children.flatMap { grateBinding(prefix, node, _, only) }
    Node.Nested(n.context, children)

  def grateBinding(prefix: names.Prefix, node: Node, b: Node.Binding, only: names.immutable.RefSet): Option[Node.Binding] =
    b match
      case Binding.Equation(lhs, rhs) =>
        if only.contains(prefix(lhs)) then Some(b) else None
      case Binding.Subnode(subnode, args) =>
        val argsX = node.subnodes(subnode).params.zip(args).flatMap { (p, e) =>
          if only.contains(prefix(names.Ref(List(subnode), p)))
          then Some(e)
          else None
        }
        val prefixX  = prefix(subnode).fullyQualifiedPath
        val required = only.exists(r => r.prefix.startsWith(prefixX))
        if required then Some(Binding.Subnode(subnode, argsX)) else None
      case Binding.Merge(scrutinee, cases) =>
        if cases.exists { case (v,n) => only.contains(prefix(n.context)) }
        then
          Some(Binding.Merge(scrutinee, cases.map { case (k,n) =>
            (k, grateNested(prefix, node, n, only))
          }))
        else
          None
      case Binding.Reset(clock, nested) =>
        if only.contains(prefix(nested.context))
        then
          Some(Binding.Reset(clock, grateNested(prefix, node, nested, only)))
        else
          None

