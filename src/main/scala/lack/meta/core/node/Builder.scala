package lack.meta.core.node

import lack.meta.macros.Location
import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.core.Sort
import lack.meta.core.term.{Exp, Flow, Val}
import lack.meta.core.Prop.{Form, Judgment}

import lack.meta.core.node.{Node => Immutable}

import scala.collection.mutable
import scala.collection.immutable

/** Mutable builder for node-based transition systems.
 */
object Builder:
  // LODO: want a program-level context that has map from var to node, list of all sorts, eg structs

  /** Mutable binding contexts */
  sealed trait Binding extends pretty.Pretty:
    def freeze(f: Freezer): Immutable.Binding
    def ppr = freeze(Freezer.ppr).ppr

  object Binding:
    class Equation(val lhs: names.Component, val rhs: Flow) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Equation(lhs, f.freeze(rhs))

    class Subnode(val subnode: names.Component, val args: List[Exp]) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Subnode(subnode, args.map(f.freeze(_)))

    class Merge(val node: Node) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Merge(
        cases.map { case (k,n) => (f.freeze(k), n.freeze(f)) }.toList
      )
      val cases: mutable.ArrayBuffer[(Exp, Nested)] = mutable.ArrayBuffer()

      def when(clock: Exp): Nested =
        val i = node.supply.freshState()
        val n = new Nested(i.name, node)
        cases += ((clock, n))
        n

    class Reset(val clock: Exp, val nested: Nested) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Reset(f.freeze(clock), nested.freeze(f))

  /** Mutable list of bindings */
  class Nested(val context: names.Component, val node: Node) extends pretty.Pretty:
    // TODO allow each nested to declare local variables
    val children: mutable.ArrayBuffer[Binding] = mutable.ArrayBuffer()

    def freeze(f: Freezer) = Immutable.Nested(context, children.map(_.freeze(f)).toList)
    def ppr = freeze(Freezer.ppr).ppr

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

  class Node(val supply: names.mutable.Supply, val path: List[names.Component]) extends pretty.Pretty:
    val params:   mutable.ArrayBuffer[names.Component]   = mutable.ArrayBuffer()
    var vars:     mutable.Map[names.Component, Variable] = mutable.Map()
    // LODO subnodes need location information
    var subnodes: mutable.Map[names.Component, Node]     = mutable.Map()
    var props:    mutable.ArrayBuffer[Judgment]          = mutable.ArrayBuffer()

    var nested: Nested = new Nested(supply.freshState().name, this)

    def freeze: Immutable =
      val freezer = Freezer(this.path)
      Immutable(
        path, params.toList,
        immutable.SortedMap.from(vars),
        immutable.SortedMap.from(subnodes.mapValues(_.freeze)),
        props.map(p => p.copy(term = freezer.freeze(p.term))).toList,
        nested.freeze(freezer))
    def ppr = freeze.ppr

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

    // LODO move smt.translate to immutable then kill these
    /** All dependent nodes in the system, including this node */
    def allNodes: Iterable[Node] =
      val subs = subnodes.values.flatMap(_.allNodes)
      // TODO: filter out non-unique nodes
      subs ++ Seq(this)

    def relies: Iterable[Judgment] =
      props.filter(_.form == Form.Rely)
    def guarantees: Iterable[Judgment] =
      props.filter(_.form == Form.Guarantee)
    def sorries: Iterable[Judgment] =
      props.filter(_.form == Form.Sorry)

  case class Freezer(path: List[names.Component]):
    def stripRef(r: names.Ref): names.Ref =
      require(r.prefix.startsWith(path),
        s"""Node ${names.Prefix(path).pprString}: invalid variable reference
        |All variable references should start with the node's path, but ${r.pprString} doesn't.
        |This may be due to an improper node invocation; see lack.meta.source.Node.Invocation.
        |Variable: ${r.pprString}
        |""".stripMargin)
      val strip = r.prefix.drop(path.length)
      names.Ref(strip, r.name)

    def freeze(exp: Exp): Exp = exp match
      case Exp.Var(s, v) =>
        Exp.Var(s, stripRef(v))
      case v: Exp.Val =>
        v
      case Exp.App(s, p, args : _*) =>
        Exp.App(s, p, args.map(freeze(_)) : _*)
      case Exp.Cast(op, e) =>
        Exp.Cast(op, freeze(e))

    def freeze(flow: Flow): Flow = flow match
      case Flow.Pure(e) =>
        Flow.Pure(freeze(e))
      case Flow.Arrow(first, later) =>
        Flow.Arrow(freeze(first), freeze(later))
      case Flow.Pre(e) =>
        Flow.Pre(freeze(e))
      case Flow.Fby(v, e) =>
        Flow.Fby(v, freeze(e))

  object Freezer:
    def ppr = Freezer(List())
