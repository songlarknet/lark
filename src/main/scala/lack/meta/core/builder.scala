package lack.meta.core.builder

import lack.meta.macros.Location
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Flow, Prim, Val}
import lack.meta.core.prop.{Form, Judgment}

import scala.collection.mutable

/** Mutable builder for node-based transition systems.
 *
 * Once the core language settles down I'd like to add a separate immutable
 * representation of nodes. For now it's easier to just use this one
 * everywhere. LODO
 */
// LODO: want a program-level context that has map from var to node, list of all sorts, eg structs

/** Mutable binding contexts */
sealed trait Binding extends pretty.Pretty
object Binding:
  class Equation(val lhs: names.Component, val rhs: Flow) extends Binding:
    def ppr = lhs.ppr <+> pretty.text("=") <+> rhs.ppr
  class Subnode(val subnode: names.Component, val args: List[Exp]) extends Binding:
    def ppr = pretty.text("Subnode") <+> subnode.ppr <> pretty.tupleP(args)

  class Merge(val node: Node) extends Binding:
    val cases: mutable.ArrayBuffer[(Exp, Nested)] = mutable.ArrayBuffer()
    def ppr =
      pretty.vsep(
        cases.zipWithIndex.map { case ((clock, nest), ix) =>
          pretty.text(if ix == 0 then "Merge When" else "Else When") <> pretty.parens(clock.ppr) <+> nest.ppr
        }.toSeq)

    def when(clock: Exp): Nested =
      val i = node.supply.freshState()
      val n = new Nested(i.name, node)
      cases += ((clock, n))
      n

  class Reset(val clock: Exp, val nested: Nested) extends Binding:
    def ppr = pretty.text("Reset") <> pretty.parens(clock.ppr) <+> nested.ppr

/** Mutable list of bindings */
class Nested(val context: names.Component, val node: Node):
  // TODO allow each nested to declare local variables
  val children: mutable.ArrayBuffer[Binding] = mutable.ArrayBuffer()

  def ppr = pretty.nest(pretty.text("@context") <> pretty.parens(context.ppr) <> pretty.colon <@>
    pretty.vsep(children.map(_.ppr).toList))

  // LODO do merging / cse on append?
  def append(b: Binding): Unit =
    children += b

  def merge(): Binding.Merge =
    val m = new Binding.Merge(node)
    append(m)
    m

  def reset(clock: Exp): Nested =
    if (clock == Exp.Val(Sort.Bool, Val.Bool(false)))
      this
    else
      val i = node.supply.freshState()
      val n = new Nested(i.name, node)
      val r = new Binding.Reset(clock, n)
      append(r)
      r.nested

  /** Create a new binding for the given streaming expression.
   * Trivial expressions (values and variables) are returned as-is with
   * no binding added.
   * */
  def memo(rhs: Flow)(using location: Location): Exp = rhs match
    case Flow.Pure(e: Exp.Var) => e
    case Flow.Pure(e: Exp.Val) => e
    case _ =>
      // Try to re-use binding if we already have one.
      //
      // TODO: apply some local rewrites, eg "v -> pre e = Fby(v, e)"
      // and const prop
      // TODO: look in other bindings.
      //
      // Maybe we want this to be as dumb as possible so that the
      // source translation is "obviously correct".
      // Then we can do better CSE in later stages.
      children.flatMap {
        case b: Binding.Equation if rhs == b.rhs =>
          val v = node.vars(b.lhs)
          assert(v.sort == rhs.sort,
            s"""When trying to reuse existing binding
              ${b.lhs} : ${v.sort} = ${b.rhs}
            for requested expression ${rhs} : ${rhs.sort} at location ${location},
            the two sorts don't match.
            """)
          Seq(node.xvar(b.lhs))
        case _ => Seq.empty
      }.headOption.getOrElse(memoForce(rhs))

  /** Create a new binding for the given expression, even for simple expressions.
   * This creates bindings for simple expressions such as variables and values;
   * doesn't reuse existing bindings.
   */
  def memoForce(rhs: Flow)(using location: Location): Exp =
    val vv = Variable(rhs.sort, location, Variable.Generated)
    val name = location.enclosing.fold(names.ComponentSymbol.LOCAL)(i => names.ComponentSymbol.fromScalaSymbol(i))
    val v = node.fresh(name, vv, forceIndex = true)
    append(new Binding.Equation(v.v.name, rhs))
    v

  def equation(lhs: names.Component, rhs: Flow): Unit =
    append(new Binding.Equation(lhs, rhs))

  def subnode(name: names.Component, subnode: Node, args: List[Exp]): Unit =
    assert(!node.vars.contains(name), s"tried to allocate a subnode named ${name} but that name is already used by variable ${node.vars(name)}")
    assert(!node.subnodes.contains(name), s"tried to allocate a subnode named ${name} but that name is already used by subnode ${node.subnodes(name)}")
    node.subnodes += name -> subnode
    append(new Binding.Subnode(name, args))

object Node:
  def top(): Node = new Node(new names.mutable.Supply(List()), List())

object Variable:
  sealed trait Mode
  case object Argument extends Mode
  case object Local extends Mode
  case object Output extends Mode
  case object Generated extends Mode

case class Variable(sort: Sort, location: Location, mode: Variable.Mode)

class Node(val supply: names.mutable.Supply, val path: List[names.Component]) extends pretty.Pretty:
  val params:   mutable.ArrayBuffer[names.Component]   = mutable.ArrayBuffer()
  var vars:     mutable.Map[names.Component, Variable] = mutable.Map()
  // LODO subnodes need location information
  var subnodes: mutable.Map[names.Component, Node]     = mutable.Map()
  var props:    mutable.ArrayBuffer[Judgment]          = mutable.ArrayBuffer()

  var nested: Nested = new Nested(supply.freshState().name, this)

  def relies: Iterable[Judgment] =
    props.filter(_.form == Form.Rely)
  def guarantees: Iterable[Judgment] =
    props.filter(_.form == Form.Guarantee)
  def sorries: Iterable[Judgment] =
    props.filter(_.form == Form.Sorry)

  /** All dependent nodes in the system, including this node */
  def allNodes: Iterable[Node] =
    val subs = subnodes.values.flatMap(_.allNodes)
    // TODO: filter out non-unique nodes
    subs ++ Seq(this)

  def fresh(name: names.ComponentSymbol, variable: Variable, forceIndex: Boolean = false): Exp.Var =
    val r = supply.freshRef(name, forceIndex)
    val v = Exp.Var(variable.sort, r)
    vars += r.name -> variable
    if (variable.mode == Variable.Argument)
      params += r.name
    v

  def freshSubnodeRef(name: names.ComponentSymbol): names.Ref =
    supply.freshRef(name) // , forceIndex = true)

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


  def prop(j: Judgment): Unit =
    props += j

  def ppr =
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

