package lack.meta.smt

import lack.meta.base.Integer
import lack.meta.core.names
import lack.meta.core.builder
import lack.meta.core.builder.Node
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}

import lack.meta.smt.solver.Solver
import lack.meta.smt.solver.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import scala.collection.mutable

object system:
  // use SortedMap here instead?
  case class Namespace(
    values: Map[names.Component, Sort] = Map(),
    namespaces: Map[names.Component, Namespace] = Map()):
      def <>(that: Namespace): Namespace =
        val values = that.values.foldLeft(this.values) { case (m,v) =>
          this.values.get(v._1).foreach { u =>
            assert(u == v._2, s"Namespace invariant failure, different sorts ${u} /= ${v._2} for component ${v._1}")
          }
          m + v
        }
        val namespaces = that.namespaces.foldLeft(this.namespaces) { case (m,n) =>
          m.get(n._1) match {
            case None => m + n
            case Some(nn) => m + (n._1 -> (nn <> n._2))
          }
        }
        Namespace(values, namespaces)
      def pretty: String =
        val vs = values.map { (k,v) => s"${k.pretty}: ${v.pretty}" }
        val ns = namespaces.map { (k,v) => s"${k.pretty}: ${v.pretty}" }
        s"{ ${(vs ++ ns).mkString("; ")} }"

  object Namespace:
    def fromRef(ref: names.Ref, sort: Sort): Namespace =
      ref.path match {
        case Nil =>
          Namespace(values = Map(ref.name -> sort))
        case p :: rest =>
          Namespace(namespaces = Map(p -> fromRef(names.Ref(rest, ref.name), sort)))
      }

  case class Prefix(prefix: List[names.Component]):
    val pfx = prefix.map(_.pretty).mkString(".")
    def apply(name: names.Ref): Terms.QualifiedIdentifier =
      compound.qid(names.Ref(prefix ++ name.path, name.name).pretty)

  object Prefix:
    val state  = Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("state"), None)) )
    val stateX = Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("stateX"), None)) )
    val row    = Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("row"), None)) )
    val oracle = Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("oracle"), None)) )

  /** Oracle supply so that systems can ask for nondeterministic choices from outside,
   * such as re-initialising delays to undefined on reset. */
  class Oracle:
    val oracles: mutable.ArrayBuffer[(Terms.SSymbol, Sort)] = mutable.ArrayBuffer()

    def oracle(path: List[names.Component], sort: Sort): Terms.QualifiedIdentifier =
      val i = oracles.length
      val name = names.Ref(path, names.Component(names.ComponentSymbol.fromStringUnsafe(""), Some(i)))
      val qid  = Prefix.oracle(name)
      oracles += (qid.id.symbol -> sort)
      qid

  /** State supply */
  class Supply(path: List[names.Component]):
    var stateIx = 0
    def state(): names.Ref =
      // want better state variables
      val ref = names.Ref(path, names.Component(names.ComponentSymbol.fromScalaSymbol("pre"), Some(stateIx)))
      stateIx = stateIx + 1
      ref

  trait System[T]:
    def state: Namespace
    def row: Namespace
    def init(oracle: Oracle, state: Prefix): Terms.Term
    def extract(oracle: Oracle, state: Prefix, row: Prefix): T
    def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term

  object System:
    def pure[T](value: T): System[T] = new System[T]:
      def state: Namespace = Namespace()
      def row: Namespace = Namespace()
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.bool(true)
      def extract(oracle: Oracle, state: Prefix, row: Prefix): T =
        value
      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        compound.bool(true)

  extension[T,U] (outer: System[T => U])
    def <*>(that: System[T]): System[U] = new System[U]:
      def state: Namespace = outer.state <> that.state
      def row: Namespace = outer.row <> that.row
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.and(
          outer.init(oracle, state),
          that.init(oracle, state))
      def extract(oracle: Oracle, state: Prefix, row: Prefix): U =
        val f = outer.extract(oracle, state, row)
        val t = that.extract(oracle, state, row)
        f(t)

      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        val xa = outer.step(oracle, state, row, stateX)
        val xb = that.step(oracle, state, row, stateX)
        compound.and(xa, xb)

  extension (outer: System[Unit])
    /** join two systems, ignoring the values */
    def <>(that: System[Unit]): System[Unit] =
      def ignore2(x: Unit)(y: Unit): Unit = ()
      System.pure(ignore2) <*> outer <*> that


  /** Defined system */
  case class SolverFunDef(name: Terms.QualifiedIdentifier, oracles: List[(Terms.SSymbol, Sort)], body: Terms.Term):
    def pretty: String = s"${name} = λ${oracles.map((a,b) => s"${a.name}: ${b.pretty}").mkString(" ")}. ${body}"

    def fundef(params: List[Terms.SortedVar]): Commands.FunDef =
      val allParams = params ++ oracles.map((v,s) => Terms.SortedVar(v, translate.sort(s)))
      Commands.FunDef(name.id.symbol, allParams, translate.sort(Sort.Bool), body)

  case class SolverNode(
    path: List[names.Component],
    state: Namespace,
    row: Namespace,
    params: List[names.Ref],
    init: SolverFunDef,
    step: SolverFunDef):
    def pretty: String =
      s"""System [${path.map(_.pretty).mkString(".")}]
         |  State:   ${state.pretty}
         |  Row:     ${row.pretty}
         |  Params:  ${params.map(_.pretty).mkString(", ")}
         |  Init:    ${init.pretty}
         |  Step:    ${step.pretty}""".stripMargin

    def paramsOfNamespace(prefix: Prefix, ns: Namespace): List[Terms.SortedVar] =
      val vs = ns.values.toList.map((v,s) => Terms.SortedVar(prefix(names.Ref(List(), v)).id.symbol, translate.sort(s)))
      val nsX = ns.namespaces.toList.flatMap((v,n) => paramsOfNamespace(Prefix(prefix.prefix :+ v), n))
      vs ++ nsX

    def fundefs: List[Commands.DefineFun] =
      val statePs  = paramsOfNamespace(Prefix.state,  state)
      val stateXPs = paramsOfNamespace(Prefix.stateX, state)
      val rowPs    = paramsOfNamespace(Prefix.row,    row)

      val initF    = init.fundef(statePs)
      val stepF    = step.fundef(statePs ++ rowPs ++ stateXPs)

      List(Commands.DefineFun(initF), Commands.DefineFun(stepF))

  case class SolverSystem(nodes: List[SolverNode], top: SolverNode):
    def fundefs: List[Commands.DefineFun] = nodes.flatMap(_.fundefs)

    def pretty: String = nodes.map(_.pretty).mkString("\n")

  object translate:
    def sort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def value(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => compound.int(i)

    class Context(val nodes: Map[List[names.Component], SolverNode], val supply: Supply)

    def nodes(inodes: Iterable[Node]): SolverSystem =
      var map = Map[List[names.Component], SolverNode]()
      val snodes = inodes.map { case inode =>
        val snode = node(new Context(map, new Supply(List())), inode)
        map += (inode.path -> snode)
        snode
      }.toList
      SolverSystem(snodes, snodes.last)

    def node(context: Context, node: Node): SolverNode =
      def nm(i: names.ComponentSymbol): names.Ref =
        names.Ref(node.path, names.Component(i, None))

      val sys = nested(context, node, None, node.nested)
      val params = node.params.map { p => names.Ref(node.path, p) }.toList

      val initO    = new Oracle()
      val stepO    = new Oracle()

      val initT    = sys.init(initO, Prefix.state)
      val stepT    = sys.step(stepO, Prefix.state, Prefix.row, Prefix.stateX)

      val initI    = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("init")).pretty)
      val stepI    = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("step")).pretty)

      val initD    = SolverFunDef(initI, initO.oracles.toList, initT)
      val stepD    = SolverFunDef(stepI, stepO.oracles.toList, stepT)

      SolverNode(node.path, sys.state, sys.row, params, initD, stepD)

    def nested(context: Context, node: Node, init: Option[names.Ref], nested: builder.Binding.Nested): System[Unit] =
      val initR = names.Ref(node.path, nested.init)
      val initN = Namespace.fromRef(initR, Sort.Bool)
      // TODO match on selector, do When/Reset
      // val selectorS = nested.selector
      val children = nested.children.map(binding(context, node, initR, _))
      val t = children.fold(System.pure(()))(_ <> _)

      new System:
        def state: Namespace = t.state <> initN
        // Dumb thing: we need the init binding in both state and row because
        // variable references to init will look inside the row, but arrow looks in state.
        def row: Namespace = t.row <> initN
        def init(oracle: Oracle, state: Prefix): Terms.Term =
          compound.and(t.init(oracle, state), state(initR))
        def extract(oracle: Oracle, state: Prefix, row: Prefix) =
          ()
        def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
          compound.and(
            t.step(oracle, state, row, stateX),
            compound.funapp("=", state(initR), row(initR)),
            compound.funapp("not", stateX(initR)))

    def binding(context: Context, node: Node, init: names.Ref, binding: builder.Binding): System[Unit] = binding match
      case builder.Binding.Equation(lhs, rhs) =>
        val t0 = expr(ExpContext(node, init, context.supply), rhs)
        val xbind = node.xvar(lhs)
        new System:
          def state: Namespace = t0.state
          def row: Namespace = t0.row <> Namespace.fromRef(xbind.v, xbind.sort)
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            t0.init(oracle, state)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            ()
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            val v = t0.extract(oracle, state, row)
            compound.and(
              compound.funapp("=", row(xbind.v), v),
              t0.step(oracle, state, row, stateX)
            )
      case builder.Binding.Subnode(subnode, args) =>
        // TODO call subnodes
        System.pure(())
      case nest: builder.Binding.Nested =>
        nested(context, node, Some(init), nest)


    class ExpContext(val node: Node, val init: names.Ref, val supply: Supply)

    def expr(context: ExpContext, exp: Exp): System[Terms.Term] = exp match
      case Exp.flow.Arrow(_, first, later) =>
        val t0 = expr(context, first)
        val t1 = expr(context, later)
        val choice = new System[Terms.Term => Terms.Term => Terms.Term]:
          def state: Namespace = Namespace.fromRef(context.init, Sort.Bool)
          def row: Namespace = Namespace()
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.bool(true)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            def choose(firstT: Terms.Term)(laterT: Terms.Term): Terms.Term =
              compound.funapp("ite", state(context.init), firstT, laterT)
            choose
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.bool(true)
        choice <*> t0 <*> t1

      case Exp.flow.Pre(sort, pre) =>
        val t0 = expr(context, pre)
        val ref = context.supply.state()
        new System[Terms.Term]:
          def state: Namespace = Namespace.fromRef(ref, sort) <> t0.state
          def row: Namespace = t0.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            val u = oracle.oracle(context.node.path, sort)
            compound.and(t0.init(oracle, state),
              compound.funapp("=", state(ref), u))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            state(ref)
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                stateX(ref),
                t0.extract(oracle, state, row)),
              t0.step(oracle, state, row, stateX))

      case Exp.flow.Fby(sort, v0, pre) =>
        val t0 = expr(context, pre)
        val ref = context.supply.state()
        new System[Terms.Term]:
          def state: Namespace = Namespace.fromRef(ref, sort) <> t0.state
          def row: Namespace = t0.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.and(
              t0.init(oracle, state),
              compound.funapp("=", state(ref), value(v0)))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            state(ref)
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                stateX(ref),
                t0.extract(oracle, state, row)),
              t0.step(oracle, state, row, stateX))

      case Exp.nondet.Undefined(sort) =>
        new System[Terms.Term]:
          def state: Namespace = Namespace()
          def row: Namespace = Namespace()
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.bool(true)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            // TODO: multiple calls to extract is weird - will allocate fresh oracles.
            // Move oracle allocation to step
            val o = oracle.oracle(context.node.path, sort)
            o
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.bool(true)

      case Exp.Val(_, v) => System.pure(value(v))
      case Exp.Var(s, v) => new System:
        def state: Namespace = Namespace()
        def row: Namespace = Namespace.fromRef(v, s)
        def init(oracle: Oracle, state: Prefix): Terms.Term =
          compound.bool(true)
        def extract(oracle: Oracle, state: Prefix, row: Prefix): Terms.Term =
          row(v)
        def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
          compound.bool(true)

      case Exp.App(sort, prim, args : _*) =>
        val zeroS = System.pure(List[Terms.Term]())
        val argsS = args.foldLeft(zeroS) { case (collectS, arg) =>
          def snoc(list: List[Terms.Term])(arg: Terms.Term): List[Terms.Term] = list :+ arg
          System.pure(snoc) <*> collectS <*> expr(context, arg)
        }

        def mkapp(argsT: List[Terms.Term]): Terms.Term =
          compound.funapp(prim.pretty, argsT : _*)

        System.pure(mkapp) <*> argsS

