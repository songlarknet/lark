package lack.meta.core.node

import lack.meta.macros.Location
import lack.meta.base.{names, pretty}
import lack.meta.core.term.{Exp, Flow}
import lack.meta.core.Prop.{Form, Judgment}

case class Node(
  path:     List[names.Component],
  params:   List[names.Component],
  vars:     names.immutable.ComponentMap[Variable],
  // LODO subnodes need location information
  subnodes: names.immutable.ComponentMap[Node],
  props:    List[Judgment],
  nested:   Node.Nested
) extends pretty.Pretty:

  def relies: Iterable[Judgment] =
    props.filter(_.form == Form.Rely)
  def guarantees: Iterable[Judgment] =
    props.filter(_.form == Form.Guarantee)
  def sorries: Iterable[Judgment] =
    props.filter(_.form == Form.Sorry)

  def xvar(name: names.Component): Exp.Var =
    val v = vars(name)
    Exp.Var(v.sort, names.Ref(path, name))

  /** Find source location of given expression.
   * LODO expressions should just contain source locations.
   */
  def locate(exp: Exp): Location = exp match
    case v : Exp.Var =>
      vars.get(v.v.name).fold(Location.empty)(_.location)
    case _ =>
      Location.empty

  def ppr = pprWithSubnodes(subnodes.toList)

  def pprWithSubnodes(subnodes: List[(names.Component, Node)]) =
    val pathP = names.Prefix(path).ppr
    val paramsP = params.map(p => p.ppr <+> pretty.colon <+> xvar(p).sort.ppr)
    val varsP = vars.map(x => pretty.value(x._2.mode) <+> x._1.ppr <+> pretty.colon <+> x._2.sort.ppr <+> x._2.location.ppr)
    val bindingsH = pretty.text("Bindings @context(") <> nested.context.ppr <> pretty.text("):")
    val bindingsP = nested.children.map(x => x.ppr)
    val subnodesP = subnodes.map(x => x._1.ppr <+> pretty.equal <+> x._2.ppr)
    val propsP = props.map(x => x.ppr)

    pretty.text("Node") <+> pretty.nest(pathP <> pretty.tuple(paramsP.toSeq) <@>
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
