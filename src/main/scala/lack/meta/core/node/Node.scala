package lack.meta.core.node

import lack.meta.macros.Location
import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.core.term
import lack.meta.core.term.{Exp, Flow}
import lack.meta.core.Prop.{Form, Judgment}

case class Node(
  name:     names.Ref,
  params:   List[names.Component],
  vars:     names.immutable.ComponentMap[Variable],
  // LODO subnodes need location information
  subnodes: names.immutable.ComponentMap[Node],
  props:    List[Judgment],
  nested:   Node.Nested
) extends pretty.Pretty:

  /** Map from context name to nested context. */
  val context: names.immutable.ComponentMap[(Node.Nested, Node.Path)] =
    val ns = Seq((nested, List())) ++ nested.allSubnesteds
    scala.collection.immutable.SortedMap.from(ns.map { n => n._1.context -> n })

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

  def ppr = pprWithSubnodes(subnodes.toList)

  def pprWithSubnodes(subnodes: List[(names.Component, Node)]) =
    val nameP = name.ppr
    val paramsP = params.map(p => p.ppr <+> pretty.colon <+> xvar(p).sort.ppr)
    val varsP = vars.map(x => pretty.value(x._2.mode) <+> x._1.ppr <+> pretty.colon <+> x._2.sort.ppr <+> x._2.location.ppr)
    val bindingsH = pretty.text("Bindings @context(") <> nested.context.ppr <> pretty.text("):")
    val bindingsP = nested.children.map(x => x.ppr)
    val subnodesP = subnodes.map(x => x._1.ppr <+> pretty.equal <+> x._2.ppr)
    val propsP = props.map(x => x.ppr)

    pretty.text("Node") <+> pretty.nest(nameP <> pretty.tuple(paramsP.toSeq) <@>
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

    case class Merge(cases: List[(Exp, Nested)]) extends Binding:
      def ppr =
        pretty.vsep(
          cases.zipWithIndex.map { case ((clock, nest), ix) =>
            pretty.text(if ix == 0 then "Merge When" else "Else When") <> pretty.parens(clock.ppr) <+> nest.ppr
          }.toSeq)

    case class Reset(clock: Exp, nested: Nested) extends Binding:
      def ppr = pretty.text("Reset") <> pretty.parens(clock.ppr) <+> nested.ppr

  /** List of bindings in the same streaming context */
  case class Nested(context: names.Component, children: List[Binding]):
    def ppr = pretty.nest(pretty.text("@context") <> pretty.parens(context.ppr) <> pretty.colon <@>
      pretty.vsep(children.map(_.ppr).toList))

    // /** Each context defines an implicit 'INIT' variable which is true when the
    //  * context has been initialised. It's equivalent to init := false -> true.
    //  */
    // val INIT = names.Ref(List(context),
    //   names.Component(names.ComponentSymbol.INIT))

    /** Map of named equation and subnode bindings in this context. */
    val bindings: names.immutable.ComponentMap[Binding] =
      scala.collection.immutable.SortedMap.from(
        children.flatMap { b => b match
          case Binding.Equation(lhs, _) =>
            Seq(lhs -> b)
          case Binding.Subnode(subnode, _) =>
            Seq(subnode -> b)
          case _ =>
            Seq()
        })

    /** Direct and indirect nested contexts inside this one. */
    def allSubnesteds: Iterable[(Nested, Path)] = children.flatMap { c => c match
      case Binding.Merge(cases) =>
        var preds = List[Exp]()
        val paths = cases.map { case (e,n) =>
          val path = Path.Entry.Merge(preds, e)
          preds = preds ++ List(e)
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
      case class Merge(not: List[Exp], yes: Exp) extends Entry:
        def clock: Exp =
          val nots = not.map(term.Compound.app(term.prim.Table.Not, _))
          val ands = nots ++ List(yes)
          ands.fold(term.Compound.val_(term.Val.Bool(false))) { (a,b) =>
            term.Compound.app(term.prim.Table.And, a, b)
          }
