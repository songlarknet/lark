package lack.meta.smt

import lack.meta.base.num.Integer
import lack.meta.base.names
import lack.meta.base.pretty
import lack.meta.core.builder
import lack.meta.core.builder.Node
import lack.meta.core.prop.Judgment
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
    namespaces: Map[names.Component, Namespace] = Map())
    extends pretty.Pretty:
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
      def ppr =
        val vs = values.map { (k,v) => k.ppr <> pretty.colon <+> v.ppr }
        val ns = namespaces.map { (k,v) => k.ppr <> pretty.colon <+> v.ppr }
        val vns = pretty.ssep((vs ++ ns).toSeq, pretty.semi <> pretty.space)
        pretty.braces(pretty.space <> vns <> pretty.space)

      def refs(prefix: Prefix): Iterable[names.Ref] =
        values.map(v => names.Ref(prefix.prefix, v._1)) ++
        namespaces.flatMap(ns => ns._2.refs(Prefix(prefix.prefix :+ ns._1)))

  object Namespace:
    def fromRef(ref: names.Ref, sort: Sort): Namespace =
      ref.prefix match {
        case Nil =>
          Namespace(values = Map(ref.name -> sort))
        case p :: rest =>
          Namespace(namespaces = Map(p -> fromRef(names.Ref(rest, ref.name), sort)))
      }

  case class Prefix(prefix: List[names.Component]) extends pretty.Pretty:
    def apply(name: names.Ref): Terms.QualifiedIdentifier =
      compound.qid(names.Ref(prefix ++ name.prefix, name.name).pprString)

    def ppr = names.Prefix(prefix).ppr

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
    def assumptions: List[SolverJudgment]
    def obligations: List[SolverJudgment]

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
      def assumptions: List[SolverJudgment] = List()
      def obligations: List[SolverJudgment] = List()

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
      def assumptions: List[SolverJudgment] = outer.assumptions ++ that.assumptions
      def obligations: List[SolverJudgment] = outer.obligations ++ that.obligations

  extension (outer: System[Unit])
    /** join two systems, ignoring the values */
    def <>(that: System[Unit]): System[Unit] =
      def ignore2(x: Unit)(y: Unit): Unit = ()
      System.pure(ignore2) <*> outer <*> that


  /** Defined system */
  case class SolverFunDef(
    name: Terms.QualifiedIdentifier,
    oracles: List[(Terms.SSymbol, Sort)],
    body: Terms.Term
  ) extends pretty.Pretty:
    def ppr =
      val oraclesP = s"λ${oracles.map((a,b) => s"(${a.name}: ${b.pprString})").mkString(" ")}."
      // LODO add nice pretty-printing to solver expressions
      pretty.string(s"${name} = ${oraclesP} ${lack.meta.smt.solver.pprTermBigAnd(body)}")

    def fundef(params: List[Terms.SortedVar]): Commands.FunDef =
      val allParams = params ++ oracles.map((v,s) => Terms.SortedVar(v, translate.sort(s)))
      Commands.FunDef(name.id.symbol, allParams, translate.sort(Sort.Bool), body)

  case class SolverJudgment(row: names.Ref, judgment: Judgment) extends pretty.Pretty:
    def ppr = row.ppr <+> pretty.equal <+> judgment.ppr

  case class SolverNode(
    path: List[names.Component],
    state: Namespace,
    row: Namespace,
    params: List[names.Ref],
    init: SolverFunDef,
    step: SolverFunDef,
    assumptions: List[SolverJudgment],
    obligations: List[SolverJudgment]
  ) extends pretty.Pretty:
    def ppr =
      pretty.text("System") <+> names.Prefix(path).ppr <@>
        pretty.subgroup("State:", List(state.ppr)) <>
        pretty.subgroup("Row:", List(row.ppr)) <>
        pretty.subgroup("Params:", List(pretty.csep(params.map(_.ppr)))) <>
        pretty.subgroup("Init:", List(init.ppr)) <>
        pretty.subgroup("Step:", List(step.ppr)) <>
        pretty.subgroup("Assumptions:", assumptions.map(_.ppr)) <>
        pretty.subgroup("Obligations:", obligations.map(_.ppr))

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

  case class SolverSystem(nodes: List[SolverNode], top: SolverNode) extends pretty.Pretty:
    def fundefs: List[Commands.DefineFun] = nodes.flatMap(_.fundefs)

    def ppr = pretty.vsep(nodes.map(_.ppr))

  object translate:
    def sort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def value(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => compound.int(i)

    class Context(val nodes: Map[List[names.Component], SolverNode], val supply: Supply)

    class ExpContext(val node: Node, val init: names.Ref, val supply: Supply):
      def stripRef(r: names.Ref): names.Ref =
        ExpContext.stripRef(node, r)

    object ExpContext:
      def stripRef(node: Node, r: names.Ref): names.Ref =
        val pfx = node.path
        require(r.prefix.startsWith(pfx), s"Ill-formed node in node ${names.Prefix(node.path).pprString}: all variable references should start with the node's path, but ${r.pprString} doesn't")
        val strip = r.prefix.drop(pfx.length)
        names.Ref(strip, r.name)

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
      val params = node.params.map { p => names.Ref(List(), p) }.toList

      val initO    = new Oracle()
      val stepO    = new Oracle()

      val initT    = sys.init(initO, Prefix.state)
      val stepT    = sys.step(stepO, Prefix.state, Prefix.row, Prefix.stateX)

      val initI    = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("init")).pprString)
      val stepI    = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("step")).pprString)

      val initD    = SolverFunDef(initI, initO.oracles.toList, initT)
      val stepD    = SolverFunDef(stepI, stepO.oracles.toList, stepT)

      def prop(judgment: Judgment): SolverJudgment =
        judgment.term match
          // LODO: deal with non-variables by creating a fresh row variable for them
          case Exp.Var(s, v) =>
            SolverJudgment(ExpContext.stripRef(node, v), judgment)

      val (obligations, assumptions) = node.props.map(prop).partition(j => j.judgment.isObligation)

      SolverNode(node.path, sys.state, sys.row, params, initD, stepD, assumptions.toList ++ sys.assumptions, obligations.toList ++ sys.obligations)

    def nested(context: Context, node: Node, init: Option[names.Ref], nested: builder.Binding.Nested): System[Unit] =
      nested.selector match
      case builder.Selector.When(k) =>
        val initR = names.Ref(List(), nested.init)
        val initN = Namespace.fromRef(initR, Sort.Bool)
        val children = nested.children.map(binding(context, node, initR, _))
        val t = children.fold(System.pure(()))(_ <> _)

        val te = init match
          case None =>
            // Blah - restructure, top level needs const clock so init=None
            require(k == Exp.Val(Sort.Bool, Val.Bool(true)))
            System.pure(compound.bool(true))
          case Some(i) =>
            // Evaluate clock in parent init context
            expr(ExpContext(node, i, context.supply), k)

        new System:
          def state: Namespace = t.state <> te.state <> initN
          def row: Namespace = t.row <> te.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.and(
              te.init(oracle, state),
              t.init(oracle, state),
              state(initR))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            ()
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            val whenStep = compound.and(
              t.step(oracle, state, row, stateX),
              compound.funapp("not", stateX(initR)))

            val whenStay = compound.and(
              this.state.refs(Prefix(List())).map { x =>
                compound.funapp("=", state(x), stateX(x))
              }.toSeq : _*)

            compound.and(
              te.step(oracle, state, row, stateX),
              compound.ite(te.extract(oracle, state, row), whenStep, whenStay))
          def assumptions: List[SolverJudgment] = t.assumptions ++ te.assumptions
          def obligations: List[SolverJudgment] = t.obligations ++ te.obligations
      case builder.Selector.Reset(k) =>
        val initR = names.Ref(List(), nested.init)
        val initN = Namespace.fromRef(initR, Sort.Bool)
        val children = nested.children.map(binding(context, node, initR, _))
        val t = children.fold(System.pure(()))(_ <> _)

        val te = init match
          case None =>
            assert(false, s"builder.Node invariant failure: top-level nested needs to be a when(true). Node ${names.Prefix(node.path).pprString}")
          case Some(i) =>
            // Evaluate clock in parent init context
            expr(ExpContext(node, i, context.supply), k)

        // We really want to existentially quantify over the reset states, so
        // we sneak a version of the state into the row variables
        val substateN = t.state <> initN
        val nestStateN = Namespace(Map(), Map(nested.init -> substateN))


        new System:
          def state: Namespace = substateN <> te.state
          def row: Namespace = t.row <> te.row <> nestStateN
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.and(
              te.init(oracle, state),
              t.init(oracle, state),
              state(initR))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            ()
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            val stateR = Prefix(row.prefix ++ List(nested.init))

            val whenReset = compound.and(
              t.init(oracle, stateR),
              stateR(initR))

            val whenStep = compound.and(
              this.state.refs(Prefix(List())).map { x =>
                compound.funapp("=", state(x), stateR(x))
              }.toSeq : _*)

            compound.and(
              te.step(oracle, state, row, stateX),
              t.step(oracle, stateR, row, stateX),
              compound.funapp("not", stateX(initR)),
              compound.ite(te.extract(oracle, state, row), whenReset, whenStep))
          def assumptions: List[SolverJudgment] = t.assumptions ++ te.assumptions
          def obligations: List[SolverJudgment] = t.obligations ++ te.obligations

    def binding(context: Context, node: Node, init: names.Ref, binding: builder.Binding): System[Unit] = binding match
      case builder.Binding.Equation(lhs, rhs) =>
        val ec = ExpContext(node, init, context.supply)
        val t0 = expr(ec, rhs)
        val xbind = node.xvar(lhs)
        val xref = names.Ref(List(), lhs)
        new System:
          def state: Namespace = t0.state
          def row: Namespace = t0.row <> Namespace.fromRef(xref, xbind.sort)
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            t0.init(oracle, state)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            ()
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            val v = t0.extract(oracle, state, row)
            compound.and(
              compound.funapp("=", row(xref), v),
              t0.step(oracle, state, row, stateX)
            )
          def assumptions: List[SolverJudgment] = t0.assumptions
          def obligations: List[SolverJudgment] = t0.obligations
      case builder.Binding.Subnode(v, args) =>
        val ec = ExpContext(node, init, context.supply)
        val subnode = node.subnodes(v)
        val subsystem = context.nodes(subnode.path)

        val argsS  = args.map(expr(ec, _))
        val argsEq = subnode.params.zip(argsS).map { (param, argT) =>
          val t0 = new System[Terms.Term => Unit]:
            def state: Namespace = Namespace()
            def row: Namespace = Namespace(Map.empty, Map(v -> subsystem.row))
            def init(oracle: Oracle, stateP: Prefix): Terms.Term =
              compound.bool(true)
            def extract(oracle: Oracle, state: Prefix, row: Prefix) =
              def const(i : Terms.Term) = ()
              const
            def step(oracle: Oracle, stateP: Prefix, rowP: Prefix, stateXP: Prefix): Terms.Term =
              val argV = argT.extract(oracle, stateP, rowP)
              val p = rowP(names.Ref(List(v), param))
              compound.funapp("=", p, argV)

            def assumptions: List[SolverJudgment] = List()
            def obligations: List[SolverJudgment] = List()
          t0 <*> argT
        }

        val subnodeT = new System[Unit]:
          def state: Namespace = Namespace(Map.empty, Map(v -> subsystem.state))
          def row: Namespace = Namespace(Map.empty, Map(v -> subsystem.row))
          def init(oracle: Oracle, stateP: Prefix): Terms.Term =
            val argsV = subsystem.paramsOfNamespace(stateP, state).map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
            val argsO = subsystem.init.oracles.map((sym, sort) => oracle.oracle(List(v), sort))
            val argsT = (argsV ++ argsO)
            Terms.FunctionApplication(subsystem.init.name, argsT)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            ()
          def step(oracle: Oracle, stateP: Prefix, rowP: Prefix, stateXP: Prefix): Terms.Term =
            val argsV = subsystem.paramsOfNamespace(stateP, state) ++ subsystem.paramsOfNamespace(rowP, row) ++ subsystem.paramsOfNamespace(stateXP, state)
            val argsO = subsystem.step.oracles.map((sym, sort) => oracle.oracle(List(v), sort))
            val argsT = (argsV.map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name))) ++ argsO)
            val stepT = Terms.FunctionApplication(subsystem.step.name, argsT)
            stepT

          // Get all of the subnode's judgments. Contract requires become
          // obligations at the use-site. Other judgments become assumptions
          // here as they've been proven in the subnode itself.
          // Should all local properties bubble up? What about sorries?
          // TODO: UNSOUND: rewrite assumptions to sofar(/\ reqs) => asms. This shouldn't matter for nodes without contracts.
          def pfx(r: names.Ref): names.Ref = names.Ref(List(v) ++ r.prefix, r.name)
          val subjudg = (subsystem.assumptions ++ subsystem.obligations).map(j => SolverJudgment(pfx(j.row), j.judgment))
          val (reqs, asms) = subjudg.partition(j => j.judgment.form == lack.meta.core.prop.Form.Require)
          def assumptions: List[SolverJudgment] = asms
          def obligations: List[SolverJudgment] = reqs.map(j => j.copy(judgment = j.judgment.copy(form = lack.meta.core.prop.Form.SubnodeRequire)))

        argsEq.foldLeft(subnodeT)(_ <> _)

      case nest: builder.Binding.Nested =>
        nested(context, node, Some(init), nest)

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
          def assumptions: List[SolverJudgment] = List()
          def obligations: List[SolverJudgment] = List()
        choice <*> t0 <*> t1

      case Exp.flow.Pre(sort, pre) =>
        val t0 = expr(context, pre)
        val ref = context.supply.state()
        new System[Terms.Term]:
          def state: Namespace = Namespace.fromRef(ref, sort) <> t0.state
          def row: Namespace = t0.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            // LODO: is the oracle necessary here? Couldn't we just leave it uninitialised?
            // Might be able to remove oracle stuff altogether
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
          def assumptions: List[SolverJudgment] = List()
          def obligations: List[SolverJudgment] = List()

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
          def assumptions: List[SolverJudgment] = List()
          def obligations: List[SolverJudgment] = List()

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
          def assumptions: List[SolverJudgment] = List()
          def obligations: List[SolverJudgment] = List()

      case Exp.Val(_, v) => System.pure(value(v))
      case Exp.Var(s, v) => new System:
        val ref = context.stripRef(v)
        // TODO HACK: should take a context describing which variables are in state and which are in row
        val rowVariable = ref.name.symbol != names.ComponentSymbol.INIT

        val ns = Namespace.fromRef(ref, s)

        def state: Namespace = if (!rowVariable) ns else Namespace()
        def row: Namespace = if (rowVariable) ns else Namespace()
        def init(oracle: Oracle, state: Prefix): Terms.Term =
          compound.bool(true)
        def extract(oracle: Oracle, state: Prefix, row: Prefix): Terms.Term =
          if (rowVariable)
            row(ref)
          else
            state(ref)
        def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
          compound.bool(true)
        def assumptions: List[SolverJudgment] = List()
        def obligations: List[SolverJudgment] = List()

      case Exp.App(sort, prim, args : _*) =>
        val zeroS = System.pure(List[Terms.Term]())
        val argsS = args.foldLeft(zeroS) { case (collectS, arg) =>
          def snoc(list: List[Terms.Term])(arg: Terms.Term): List[Terms.Term] = list :+ arg
          System.pure(snoc) <*> collectS <*> expr(context, arg)
        }

        def mkapp(argsT: List[Terms.Term]): Terms.Term =
          compound.funapp(prim.pprString, argsT : _*)

        System.pure(mkapp) <*> argsS

