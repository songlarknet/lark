package lark.meta.core.node

import lark.meta.macros.Location
import lark.meta.base.{names, pretty}
import lark.meta.base.names.given
import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow, Val}
import lark.meta.core.Prop.{Form, Judgment}

import scala.collection.mutable

case class Node(
  klass:    names.Ref,
  metas:    List[Meta],
  params:   List[names.Component],
  vars:     names.immutable.ComponentMap[Variable],
  // LODO subnodes need location information
  // LODO should subnodes be name references rather than objects? it makes transforms a bit tedious
  subnodes: names.immutable.ComponentMap[Node],
  props:    List[Judgment],
  nested:   Node.Nested
) extends pretty.Pretty:

  val prefix = names.Prefix(klass.fullyQualifiedPath)

  val allSubnesteds = Seq((nested, List())) ++ nested.allSubnesteds

  /** Map from context name to nested context. */
  val context: names.immutable.ComponentMap[(Node.Nested, Node.Path)] =
    val ns = allSubnesteds.map { n => n._1.context -> n }
    scala.collection.immutable.SortedMap.from(ns)

  /** All dependent nodes in the system, including this node */
  def allNodes: Iterable[Node] =
    allNodesDistinct(mutable.Map.empty)

  private def allNodesDistinct(mpSeen: mutable.Map[names.Ref, Node]): Iterable[Node] =
    val subs = subnodes.values.flatMap(_.allNodesDistinct(mpSeen))
    mpSeen.put(klass, this) match
      case None =>
        subs ++ Seq(this)
      case Some(value) =>
        subs

  def relies: Iterable[Judgment] =
    props.filter(_.form == Form.Rely)
  def guarantees: Iterable[Judgment] =
    props.filter(_.form == Form.Guarantee)
  def sorries: Iterable[Judgment] =
    props.filter(_.form == Form.Sorry)

  /** Get expression variable to refer to given component.
   * Exception if there is no variable with given name.
   */
  def xvar(name: names.Component): Exp.Var =
    val v = vars(name)
    Exp.Var(v.sort, names.Ref.fromComponent(name))

  def ppr = pprWithSubnodes(List())
  def pprSubnodes = pprWithSubnodes(subnodes.toList)

  def pprWithSubnodes(subnodes: List[(names.Component, Node)]) =
    val klassP = klass.ppr
    val metasP = metas.map(p => pretty.text(p.name) <+> pretty.equal <+> pretty.value(p.any))
    val paramsP = params.map(p => p.ppr <+> pretty.colon <+> xvar(p).sort.ppr)
    val varsP = vars.map(x => pretty.value(x._2.mode) <+> x._1.ppr <+> pretty.colon <+> x._2.sort.ppr <+> x._2.location.ppr)
    val bindingsH = pretty.text("Bindings @context(") <> nested.context.ppr <> pretty.text("):")
    val bindingsP = nested.children.map(x => x.ppr)
    val subnodesP = subnodes.map(x => x._1.ppr <+> pretty.equal <+> x._2.ppr)
    val propsP = props.map(x => x.ppr)

    pretty.text("Node") <+> pretty.nest(klassP <> pretty.tuple(metasP.toSeq ++ paramsP.toSeq) <@>
      pretty.subgroup("Vars:", varsP.toSeq) <>
      pretty.subgroup(bindingsH, bindingsP.toSeq) <>
      pretty.subgroup("Subnodes:", subnodesP.toSeq) <>
      pretty.subgroup("Props:", propsP.toSeq))


object Node:
  /** Bindings */
  sealed trait Binding extends pretty.Pretty
  object Binding:
    case class Equation(lhs: names.Component, rhs: Flow) extends Binding:
      def ppr = lhs.ppr <+> pretty.text("=") <+> rhs.ppr
    case class Subnode(subnode: names.Component, args: List[Exp]) extends Binding:
      def ppr = pretty.text("Subnode") <+> subnode.ppr <> pretty.tupleP(args)

    /** Non-compound bindings with no nesting */
    type Simple = Equation | Subnode

    case class Merge(scrutinee: Exp, cases: List[(Val, Nested)]) extends Binding:
      def ppr =
        pretty.text("Merge") <> pretty.parens(scrutinee.ppr) <> pretty.nest(pretty.colon <@>
        pretty.vsep(
          cases.zipWithIndex.map { case ((value, nest), ix) =>
            pretty.text("Match") <> pretty.parens(value.ppr) <+> nest.ppr
          }.toSeq))

    case class Reset(clock: Exp, nested: Nested) extends Binding:
      def ppr = pretty.text("Reset") <> pretty.parens(clock.ppr) <+> nested.ppr

  /** List of bindings in the same streaming context */
  case class Nested(context: names.Component, children: List[Binding]):
    def ppr = pretty.nest(pretty.text("@context") <> pretty.parens(context.ppr) <> pretty.colon <@>
      pretty.vsep(children.map(_.ppr).toList))

    def requiresInitFlag: Boolean =
      children.exists(b => b match
        case Binding.Equation(lhs, Flow.Arrow(_, _)) => true
        case _ => false)

    // /** Each context defines an implicit 'INIT' variable which is true when the
    //  * context has been initialised. It's equivalent to init := false -> true.
    //  */
    // val INIT = names.Ref(List(context),
    //   names.Component(names.ComponentSymbol.INIT))

    /** Map of named equation and subnode bindings in this context. */
    val bindings: names.immutable.ComponentMap[Binding.Simple] =
      scala.collection.immutable.SortedMap.from(
        children.flatMap { b => b match
          case b @ Binding.Equation(lhs, _) =>
            Seq(lhs -> b)
          case b @ Binding.Subnode(subnode, _) =>
            Seq(subnode -> b)
          case _ =>
            Seq()
        })

    /** Direct and indirect nested contexts inside this one. */
    def allSubnesteds: Iterable[(Nested, Path)] = children.flatMap { c => c match
      case Binding.Merge(scrutinee, cases) =>
        val paths = cases.map { case (v,n) =>
          val path = Path.Entry.Merge(scrutinee, v)
          (n, path)
        }
        paths.flatMap { case (n,p) =>
          val ns = Seq((n, List())) ++ n.allSubnesteds
          ns.map { case (n, pX) => (n, p :: pX) }
        }
      case Binding.Reset(k, n) =>
        val ns = Seq((n, List())) ++ n.allSubnesteds
        ns.map { case (n,p) => (n, Path.Entry.Reset(k) :: p) }
      case _ =>
        Nil
    }

  /** A path describes the list of reset and merge contexts that a binding can
   * be nested inside. */
  type Path = List[Path.Entry]
  object Path:
    sealed trait Entry
    object Entry:
      /** Reset when clock expression is true. */
      case class Reset(clock: Exp) extends Entry
      /** One arm of a multi-arm merge. The list `not` contains the conditions
       * of the previous arms of the merge, and `yes` contains the condition for
       * this arm. The arm is active when the conditions of the previous arms are
       * false and this one is true.
       */
      case class Merge(scrutinee: Exp, value: Val) extends Entry:
        def clock: Exp =
          term.Compound.app(term.prim.Table.Eq, scrutinee, term.Compound.val_(value))
