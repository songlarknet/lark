package lark.meta.core.node

import lark.meta.macros.Location
import lark.meta.base.{names, pretty}
import lark.meta.base.names.given
import lark.meta.core.Sort
import lark.meta.core.term.{Exp, Flow, Val}
import lark.meta.core.Prop.{Form, Judgment}

import lark.meta.core.node.{Node => Immutable}

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

    class Merge(val clock: Exp, val node: Node) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Merge(
        f.freeze(clock),
        cases.map { case (v,n) => (v, n.freeze(f)) }.toList
      )
      val cases: mutable.ArrayBuffer[(Val, Nested)] = mutable.ArrayBuffer()

      def when(value: Val): Nested =
        val i = node.supply.freshState()
        val n = new Nested(i.name, node)
        cases += ((value, n))
        n

    class Reset(val clock: Exp, val nested: Nested) extends Binding:
      def freeze(f: Freezer) = Immutable.Binding.Reset(f.freeze(clock), nested.freeze(f))

  /** Mutable list of bindings */
  class Nested(val context: names.Component, val node: Node) extends pretty.Pretty:
    // TODO allow each nested to declare local variables
    val children: mutable.ArrayBuffer[Binding] = mutable.ArrayBuffer()

    def freeze(f: Freezer) = Immutable.Nested(context, children.map(_.freeze(f)).toList)
    def ppr = freeze(Freezer.ppr).ppr

    def append(b: Binding): Unit =
      children += b

    def merge(scrutinee: Exp): Binding.Merge =
      val m = new Binding.Merge(scrutinee, node)
      append(m)
      m

    def reset(clock: Exp): Nested =
      if (clock == Exp.Val(Val.Bool(false)))
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
        // This originally tried to re-use bindings, but it made the programs
        // a bit uglier. I think we want to do a more meaningful CSE at a later
        // stage.
        memoForce(rhs)


    /** Create a new binding for the given expression, even for simple expressions.
     * This creates bindings for simple expressions such as variables and values;
     * doesn't reuse existing bindings.
     */
    def memoForce(rhs: Flow)(using location: Location): Exp =
      val vv = Variable(rhs.sort, location, Variable.Generated)
      // TODO: fromScalaSymbol(i) should fall back on failure, currently broken for operator names such as ==
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
    def top(): Node = new Node(new names.mutable.Supply(List()), List(),
      names.Ref.fromComponent(names.Component(names.ComponentSymbol.fromScalaSymbol("<top>"))))

  class Node(val supply: names.mutable.Supply, val path: List[names.Component], val klass: names.Ref) extends pretty.Pretty:
    /** Concrete meta-arguments that this node has been applied to. */
    val metas:    mutable.ArrayBuffer[Meta]              = mutable.ArrayBuffer()
    val params:   mutable.ArrayBuffer[names.Component]   = mutable.ArrayBuffer()
    var vars:     mutable.Map[names.Component, Variable] = mutable.Map()
    // LODO subnodes need location information
    var subnodes: mutable.Map[names.Component, Node]     = mutable.Map()
    var props:    mutable.ArrayBuffer[Judgment]          = mutable.ArrayBuffer()

    var nested: Nested = new Nested(supply.freshState(forceIndex = false).name, this)

    def freeze: Immutable = Freezer.node(this)

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

  case class Freezer(path: List[names.Component]):
    def stripRef(r: names.Ref): names.Ref =
      require(r.prefix.startsWith(path),
        s"""Node ${names.Prefix(path).pprString}: invalid variable reference
        |All variable references should start with the node's path, but ${r.pprString} doesn't.
        |This may be due to an improper node invocation; see lark.meta.source.Node.Invocation.
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

    def node(n: Node): Immutable =
      node(n, mutable.Map.empty)

    /** The un-frozen representation can have klass name clashes when the same
     * klass is instantiated with different meta-arguments.
     * Freezing splits them out into separate klasses and checks that all
     * instances of the same klass with the same meta-arguments are exactly
     * equivalent. */
    def node(n: Node, mpNodes: mutable.Map[names.Ref, mutable.Map[List[Meta], Immutable]]): Immutable =
      val freezer   = Freezer(n.path)
      val metasF    = n.metas.toList
      val subnodesF = immutable.SortedMap.from(n.subnodes.mapValues(node(_, mpNodes)))
      def frozen(klassF: names.Ref) = Immutable(
          klassF, metasF, n.params.toList,
          immutable.SortedMap.from(n.vars),
          subnodesF,
          n.props.map(p => p.copy(term = freezer.freeze(p.term))).toList,
          n.nested.freeze(freezer))
      def klassIx(i: Int): names.Ref =
        n.klass.name.ix match
          case None =>
            names.Ref(n.klass.prefix, names.Component(n.klass.name.symbol, Some(i)))
          case Some(value) =>
            names.Ref(n.klass.fullyQualifiedPath, names.Component(names.ComponentSymbol.LOCAL, Some(i)))


      val mpKlasses = mpNodes.getOrElse(n.klass, mutable.Map.empty)
      mpKlasses.get(metasF) match
        case None =>
          val k =
            if metasF.isEmpty
            then n.klass
            else klassIx(mpKlasses.size)
          val nF = frozen(k)
          assert(!mpNodes.contains(k),
            s"""Tried to generate a fresh class name ${k.pprString} based on original name ${n.klass.pprString} but already in use""")
          mpKlasses.put(metasF, nF)
          mpNodes.put(n.klass, mpKlasses)
          nF
        case Some(nF0) =>
          val nF = frozen(nF0.klass)
          assert(nF == nF0,
            s"""Unstable node ${n.klass.pprString}.
              | Node ${n.klass.pprString} with meta-arguments (${metasF.mkString(", ")}) is instantiated multiple
              | times with the same meta-arguments, but the generated code is different.
              | This may mean that there are some arguments that aren't being freshened properly.
              | TODO: clean up freshening, explain fix
              |
              | Original node:
              |  ${nF0.pprString}
              | Second node:
              |  ${nF.pprString}
              |""".stripMargin)
          nF0
