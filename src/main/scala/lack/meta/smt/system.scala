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

  case class Prefix(prefix: names.Ref):
    def apply(name: names.Ref): Terms.Term =
      compound.qid(prefix.pretty + "/" + name.pretty)

  /** Oracle supply so that systems can ask for nondeterministic choices from outside,
   * such as re-initialising delays to undefined on reset. */
  class Oracle:
    val oracles: mutable.ArrayBuffer[(Terms.SSymbol, Sort)] = mutable.ArrayBuffer()

    def oracle(prefix: names.Ref, sort: Sort): Terms.Term =
      val i = oracles.length
      val sym = compound.sym(s"oracle?${prefix.pretty}?${i}")
      oracles += (sym -> sort)
      Terms.QualifiedIdentifier(Terms.Identifier(sym))

  /** State supply */
  class Supply(prefix: List[names.Component]):
    var stateIx = 0
    def state(): names.Ref =
      // want better state variables
      val ref = names.Ref(prefix, names.Component(names.ComponentSymbol.fromInternal("state"), Some(stateIx)))
      stateIx = stateIx + 1
      ref

  trait System[T]:
    def state: Namespace
    def row: Namespace
    def init(oracle: Oracle, state: Prefix): Terms.Term
    def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, T)
    def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term

  object System:
    def pure[T](value: T): System[T] = new System[T]:
      def state: Namespace = Namespace()
      def row: Namespace = Namespace()
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.bool(true)
      def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, T) =
        (compound.bool(true), value)
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
      def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, U) =
        val (xa, f) = outer.extract(oracle, state, row)
        val (xb, t) = that.extract(oracle, state, row)
        (compound.and(xa, xb), f(t))

      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        val xa = outer.step(oracle, state, row, stateX)
        val xb = that.step(oracle, state, row, stateX)
        compound.and(xa, xb)

  extension (outer: System[Unit])
    /** join two systems, ignoring the values */
    def <>(that: System[Unit]): System[Unit] = new System[Unit]:
      def state: Namespace = outer.state <> that.state
      def row: Namespace = outer.row <> that.row
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.and(
          outer.init(oracle, state),
          that.init(oracle, state))
      def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, Unit) =
        val (xa, _) = outer.extract(oracle, state, row)
        val (xb, _) = that.extract(oracle, state, row)
        (compound.and(xa, xb), ())

      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        val xa = outer.step(oracle, state, row, stateX)
        val xb = that.step(oracle, state, row, stateX)
        compound.and(xa, xb)

  /** Defined system */
  case class SolverDefinition(name: Terms.QualifiedIdentifier, oracles: List[(Terms.SSymbol, Sort)], body: Terms.Term):
    def pretty: String = s"${name} = λ${oracles.map((a,b) => s"${a.name}: ${b.pretty}").mkString(" ")}. ${body}"
  case class SolverSystem(
    path: List[names.Component],
    state: Namespace,
    row: Namespace,
    params: List[names.Ref],
    init: SolverDefinition,
    extract: SolverDefinition,
    step: SolverDefinition):
    def pretty: String =
      s"""System [${path.map(_.pretty).mkString(".")}]
         |  State:   ${state.pretty}
         |  Row:     ${row.pretty}
         |  Params:  ${params.map(_.pretty).mkString(", ")}
         |  Init:    ${init.pretty}
         |  Extract: ${extract.pretty}
         |  Step:    ${step.pretty}""".stripMargin

  object translate:
    def sort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def value(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => compound.int(i)

    class Context(val nodes: Map[List[names.Component], SolverSystem], val supply: Supply)

    def nodes(inodes: Iterable[Node]): List[SolverSystem] =
      var map = Map[List[names.Component], SolverSystem]()
      inodes.map { case inode =>
        val system = node(new Context(map, new Supply(List())), inode)

        println(system.pretty)

        map += (inode.path -> system)
        system
      }.toList

    def node(context: Context, node: Node): SolverSystem =
      def nm(i: names.ComponentSymbol): names.Ref =
        names.Ref(node.path, names.Component(i, None))

      val sys = nested(context, node, None, node.nested)
      val params = node.params.map { p => names.Ref(node.path, p) }.toList
      val state  = Prefix(names.Ref(List(), names.Component(names.ComponentSymbol.fromScalaSymbol("state"), None)) )
      val stateX = Prefix(names.Ref(List(), names.Component(names.ComponentSymbol.fromScalaSymbol("stateX"), None)) )
      val row    = Prefix(names.Ref(List(), names.Component(names.ComponentSymbol.fromScalaSymbol("row"), None)) )

      val initO    = new Oracle()
      val extractO = new Oracle()
      val stepO    = new Oracle()

      val initT    = sys.init(initO, state)
      val extractT = sys.extract(extractO, state, row)._1
      val stepT    = sys.step(stepO, state, row, stateX)

      val initI    = compound.qid(nm(names.ComponentSymbol.fromInternal("init")).pretty)
      val extractI = compound.qid(nm(names.ComponentSymbol.fromInternal("extract")).pretty)
      val stepI    = compound.qid(nm(names.ComponentSymbol.fromInternal("step")).pretty)

      val initD    = SolverDefinition(initI, initO.oracles.toList, initT)
      val extractD = SolverDefinition(extractI, extractO.oracles.toList, extractT)
      val stepD    = SolverDefinition(stepI, stepO.oracles.toList, stepT)

      SolverSystem(node.path, sys.state, sys.row, params, initD, extractD, stepD)

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
        // TODO: splitting out extract and step makes reset hard, merge back in
        def extract(oracle: Oracle, state: Prefix, row: Prefix) =
          val (tx, _) = t.extract(oracle, state, row)
          (compound.and(
            tx,
            compound.funapp("=", state(initR), row(initR))), ())
        def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
          compound.and(
            t.step(oracle, state, row, stateX),
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
            val (t, v) = t0.extract(oracle, state, row)
            (compound.and(t, compound.funapp("=", row(xbind.v), v)), ())
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            t0.step(oracle, state, row, stateX)
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
            val sym = state(context.init)
            def choose(firstT: Terms.Term)(laterT: Terms.Term): Terms.Term =
              compound.funapp("ite", sym, firstT, laterT)
            (compound.bool(true), choose)
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
            val u = oracle.oracle(state.prefix, sort)
            compound.and(t0.init(oracle, state),
              compound.funapp("=", state(ref), u))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            (compound.bool(true), state(ref))
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                stateX(ref),
                t0.extract(oracle, state, row)._2),
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
            (compound.bool(true), state(ref))
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                stateX(ref),
                t0.extract(oracle, state, row)._2),
              t0.step(oracle, state, row, stateX))

      case Exp.nondet.Undefined(sort) =>
        new System[Terms.Term]:
          def state: Namespace = Namespace()
          def row: Namespace = Namespace()
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.bool(true)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            val o = oracle.oracle(state.prefix, sort)
            (compound.bool(true), o)
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.bool(true)

      case Exp.Val(_, v) => System.pure(value(v))
      case Exp.Var(s, v) => new System:
        def state: Namespace = Namespace()
        def row: Namespace = Namespace.fromRef(v, s)
        def init(oracle: Oracle, state: Prefix): Terms.Term =
          compound.bool(true)
        def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, Terms.Term) =
          val sym = row(v)
          (compound.bool(true), sym)
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

