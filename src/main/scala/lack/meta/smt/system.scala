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

  object Prefix:
    val state  = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("state"), None)) )
    val stateX = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("stateX"), None)) )
    val row    = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("row"), None)) )

  type Namespace = names.Namespace[Sort]

  trait System[T]:
    def state: Namespace =
      names.Namespace()
    def row: Namespace =
      names.Namespace()
    def init(state: names.Prefix): Terms.Term =
      compound.bool(true)
    def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix): (Terms.Term, T)
    def assumptions: List[SolverJudgment] = List()
    def obligations: List[SolverJudgment] = List()

  object System:
    def pure[T](value: T): System[T] = new System[T]:
      def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
        (compound.bool(true), value)

    def state(ref: names.Ref, sort: Sort): System[Terms.Term] = new System:
      override def state: Namespace = names.Namespace.fromRef(ref, sort)
      def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
        (compound.bool(true), compound.qid(state(ref)))

    def stateX(ref: names.Ref, sort: Sort): System[Terms.Term] = new System:
      override def state: Namespace = names.Namespace.fromRef(ref, sort)
      def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
        (compound.bool(true), compound.qid(stateX(ref)))

    def row(ref: names.Ref, sort: Sort): System[Terms.Term] = new System:
      override def row: Namespace = names.Namespace.fromRef(ref, sort)
      def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
        (compound.bool(true), compound.qid(row(ref)))

    def conjoin(systems: Seq[System[Unit]]): System[Unit] =
      systems.fold(System.pure(()))(_ <<*> _)

  extension[T,U] (outer: System[T => U])
    def <*>(that: System[T]): System[U] = new System[U]:
      override def state: Namespace = outer.state <> that.state
      override def row: Namespace = outer.row <> that.row
      override def init(state: names.Prefix): Terms.Term =
        compound.and(
          outer.init(state),
          that.init(state))
      def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix): (Terms.Term, U) =
        val (xf, f) = outer.step(state, row, stateX)
        val (xt, t) = that.step(state, row, stateX)
        (compound.and(xf, xt), f(t))
      override def assumptions: List[SolverJudgment] = outer.assumptions ++ that.assumptions
      override def obligations: List[SolverJudgment] = outer.obligations ++ that.obligations

  extension[T] (outer: System[T])
    /** join two systems */
    def ap2[U, V](that: System[U])(f: (T, U) => V): System[V] =
      System.pure((t: T) => (u: U) => f(t,u)) <*> outer <*> that

    /** join two systems, tupling the values together */
    def <&>[U](that: System[U]): System[(T,U)] =
      ap2(that)((_,_))

    /** join two systems, taking the first value */
    def <<*>[U](that: System[U]): System[T] =
      ap2(that)((t,u) => t)

    def map[U](f: T => U): System[U] =
      System.pure(f) <*> outer

    // XXX: can't implement real bind because the "init" and "step" might take different state prefixes...
    def bind[U](f : (names.Prefix, names.Prefix, names.Prefix, T) => (Terms.Term, U)): System[U] =
      new System[U]:
        override def state: Namespace = outer.state
        override def row: Namespace = outer.row
        override def init(state: names.Prefix): Terms.Term =
          outer.init(state)
        def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix): (Terms.Term, U) =
          val (xt, t) = outer.step(state, row, stateX)
          val (xu, u) = f(state, row, stateX, t)
          (compound.and(xt, xu), u)
        override def assumptions: List[SolverJudgment] = outer.assumptions
        override def obligations: List[SolverJudgment] = outer.obligations

    def assertStep(f : T => Terms.Term): System[Unit] = bind {
        (state, row, stateX, t) =>
          (f(t), ())
      }

  /** Defined system */
  case class SolverFunDef(
    name: Terms.QualifiedIdentifier,
    body: Terms.Term
  ) extends pretty.Pretty:
    def ppr =
      // LODO add nice pretty-printing to solver expressions
      pretty.string(s"${name} = ${lack.meta.smt.solver.pprTermBigAnd(body)}")

    def fundef(params: List[Terms.SortedVar]): Commands.FunDef =
      Commands.FunDef(name.id.symbol, params, translate.sort(Sort.Bool), body)

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

    def paramsOfNamespace(prefix: names.Prefix, ns: Namespace): List[Terms.SortedVar] =
      val vs = ns.values.toList.map((v,s) => Terms.SortedVar(compound.qid(prefix(names.Ref(List(), v))).id.symbol, translate.sort(s)))
      val nsX = ns.namespaces.toList.flatMap((v,n) => paramsOfNamespace(names.Prefix(prefix.prefix :+ v), n))
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

    class Context(val nodes: Map[List[names.Component], SolverNode], val supply: names.mutable.Supply)

    class ExpContext(val node: Node, val init: names.Ref, val supply: names.mutable.Supply):
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
        val snode = node(new Context(map, new names.mutable.Supply(List())), inode)
        map += (inode.path -> snode)
        snode
      }.toList
      SolverSystem(snodes, snodes.last)

    def node(context: Context, node: Node): SolverNode =
      def nm(i: names.ComponentSymbol): names.Ref =
        names.Ref(node.path, names.Component(i, None))

      val sys        = nested(context, node, None, node.nested)
      val params     = node.params.map { p => names.Ref(List(), p) }.toList

      val initT      = sys.init(Prefix.state)
      val (stepT, _) = sys.step(Prefix.state, Prefix.row, Prefix.stateX)

      val initI      = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("init")).pprString)
      val stepI      = compound.qid(nm(names.ComponentSymbol.fromScalaSymbol("step")).pprString)

      val initD      = SolverFunDef(initI, initT)
      val stepD      = SolverFunDef(stepI, stepT)

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
        val initN = names.Namespace.fromRef[Sort](initR, Sort.Bool)
        val children = nested.children.map(binding(context, node, initR, _))
        val t = System.conjoin(children.toSeq)

        val te = init match
          case None =>
            // Blah - restructure, top level needs const clock so init=None
            require(k == Exp.Val(Sort.Bool, Val.Bool(true)))
            System.pure(compound.bool(true))
          case Some(i) =>
            // Evaluate clock in parent init context
            expr(ExpContext(node, i, context.supply), k)

        new System:
          override def state: Namespace = t.state <> te.state <> initN
          override def row: Namespace = t.row <> te.row
          override def init(state: names.Prefix): Terms.Term =
            compound.and(
              te.init(state),
              t.init(state),
              compound.qid(state(initR)))
          def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
            val (tstep, _) = t.step(state, row, stateX)
            val (testep, teclock) = te.step(state, row, stateX)
            val whenStep = compound.and(
              tstep,
              compound.funapp("not", compound.qid(stateX(initR))))

            val whenStay = compound.and(
              this.state.refs(names.Prefix(List())).map { x =>
                compound.funapp("=", compound.qid(state(x)), compound.qid(stateX(x)))
              }.toSeq : _*)

            (compound.and(
              testep,
              compound.ite(teclock, whenStep, whenStay)), ())
          override def assumptions: List[SolverJudgment] = t.assumptions ++ te.assumptions
          override def obligations: List[SolverJudgment] = t.obligations ++ te.obligations
      case builder.Selector.Reset(k) =>
        val initR = names.Ref(List(), nested.init)
        val initN = names.Namespace.fromRef[Sort](initR, Sort.Bool)
        val children = nested.children.map(binding(context, node, initR, _))
        val t = System.conjoin(children.toSeq)

        val te = init match
          case None =>
            assert(false, s"builder.Node invariant failure: top-level nested needs to be a when(true). Node ${names.Prefix(node.path).pprString}")
          case Some(i) =>
            // Evaluate clock in parent init context
            expr(ExpContext(node, i, context.supply), k)

        // We really want to existentially quantify over the reset states, so
        // we sneak a version of the state into the row variables
        val substateN = t.state <> initN
        val nestStateN = names.Namespace.nest(nested.init, substateN)

        new System:
          override def state: Namespace = substateN <> te.state
          override def row: Namespace = t.row <> te.row <> nestStateN
          override def init(state: names.Prefix): Terms.Term =
            compound.and(
              te.init(state),
              t.init(state),
              compound.qid(state(initR)))
          def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
            val stateR = names.Prefix(row.prefix ++ List(nested.init))

            val (testep, teclock) = te.step(state, row, stateX)
            val (tstepR, _) = t.step(stateR, row, stateX)

            val whenReset = compound.and(
              t.init(stateR),
              compound.qid(stateR(initR)))

            val whenStep = compound.and(
              this.state.refs(names.Prefix(List())).map { x =>
                compound.funapp("=", compound.qid(state(x)), compound.qid(stateR(x)))
              }.toSeq : _*)

            (compound.and(
              testep,
              tstepR,
              compound.funapp("not", compound.qid(stateX(initR))),
              compound.ite(teclock, whenReset, whenStep)), ())
          override def assumptions: List[SolverJudgment] = t.assumptions ++ te.assumptions
          override def obligations: List[SolverJudgment] = t.obligations ++ te.obligations

    def binding(context: Context, node: Node, init: names.Ref, binding: builder.Binding): System[Unit] = binding match
      case builder.Binding.Equation(lhs, rhs) =>
        val ec = ExpContext(node, init, context.supply)
        val t0 = expr(ec, rhs)
        val xbind = node.xvar(lhs)
        val xref = names.Ref(List(), lhs)
        (System.row(xref, xbind.sort) <&> expr(ec, rhs)).assertStep { ts =>
          compound.funapp("=", ts._1, ts._2)
        }

      case builder.Binding.Subnode(v, args) =>
        val ec = ExpContext(node, init, context.supply)
        val subnode = node.subnodes(v)
        val subsystem = context.nodes(subnode.path)

        val argsT  = args.map(expr(ec, _))

        val argsEq = subnode.params.zip(argsT).map { (param, argT) =>
          argT.bind { (state, row, stateX, argV) =>
            val p = compound.qid(row(names.Ref(List(v), param)))
            (compound.funapp("=", p, argV), ())
          }
        }

        val subnodeT = new System[Unit]:
          override def state: Namespace = names.Namespace.nest(v, subsystem.state)
          override def row: Namespace = names.Namespace.nest(v, subsystem.row)
          override def init(stateP: names.Prefix): Terms.Term =
            val argsV = subsystem.paramsOfNamespace(stateP, state).map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
            Terms.FunctionApplication(subsystem.init.name, argsV)
          def step(stateP: names.Prefix, rowP: names.Prefix, stateXP: names.Prefix) =
            val argsV =
              subsystem.paramsOfNamespace(stateP, state) ++
              subsystem.paramsOfNamespace(rowP, row) ++
              subsystem.paramsOfNamespace(stateXP, state)
            val argsT = argsV.map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
            val stepT = Terms.FunctionApplication(subsystem.step.name, argsT)
            (stepT, ())

          // Get all of the subnode's judgments. Contract requires become
          // obligations at the use-site. Other judgments become assumptions
          // here as they've been proven in the subnode itself.
          // Should all local properties bubble up? What about sorries?
          // TODO: UNSOUND: rewrite assumptions to sofar(/\ reqs) => asms. This shouldn't matter for nodes without contracts.
          def pfx(r: names.Ref): names.Ref = names.Ref(List(v) ++ r.prefix, r.name)
          val subjudg = (subsystem.assumptions ++ subsystem.obligations).map(j => SolverJudgment(pfx(j.row), j.judgment))
          val (reqs, asms) = subjudg.partition(j => j.judgment.form == lack.meta.core.prop.Form.Require)
          override def assumptions: List[SolverJudgment] = asms
          override def obligations: List[SolverJudgment] = reqs.map(j => j.copy(judgment = j.judgment.copy(form = lack.meta.core.prop.Form.SubnodeRequire)))

        System.conjoin(subnodeT :: argsEq.toList)

      case nest: builder.Binding.Nested =>
        nested(context, node, Some(init), nest)

    def expr(context: ExpContext, exp: Exp): System[Terms.Term] = exp match
      case Exp.flow.Arrow(_, first, later) =>
        val st = System.state(context.init, Sort.Bool)
        val t0 = expr(context, first)
        val t1 = expr(context, later)
        (st <&> (t0 <&> t1)).map { case (init, (first, later)) =>
          compound.ite(init, first, later)
        }

      case Exp.flow.Pre(sort, pre) =>
        val t0 = expr(context, pre)
        val ref = context.supply.freshRef(names.ComponentSymbol.PRE, forceIndex = true)
        val tinit = new System[Unit]:
          override def state: Namespace = names.Namespace.fromRef[Sort](ref, sort)
          override def init(state: names.Prefix): Terms.Term =
            compound.bool(true)
          def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
            (compound.bool(true), ())

        t0.bind { (state, row, stateX, v) =>
          (compound.funapp("=", compound.qid(stateX(ref)), v),
          compound.qid(state(ref)))
        } <<*> tinit

      case Exp.flow.Fby(sort, v0, pre) =>
        val t0 = expr(context, pre)
        val ref = context.supply.freshRef(names.ComponentSymbol.FBY, forceIndex = true)
        val tinit = new System[Unit]:
          override def state: Namespace = names.Namespace.fromRef[Sort](ref, sort)
          override def init(state: names.Prefix): Terms.Term =
            compound.funapp("=", compound.qid(state(ref)), value(v0))
          def step(state: names.Prefix, row: names.Prefix, stateX: names.Prefix) =
            (compound.bool(true), ())
        t0.bind { (state, row, stateX, v) =>
          (compound.funapp("=", compound.qid(stateX(ref)), v),
          compound.qid(state(ref)))
        } <<*> tinit

      case Exp.nondet.Undefined(sort) =>
        val ref = context.supply.freshRef(names.ComponentSymbol.UNDEFINED, forceIndex = true)
        System.row(ref, sort)

      case Exp.Val(_, v) => System.pure(value(v))
      case Exp.Var(sort, v) =>
        val ref = context.stripRef(v)
        // TODO HACK: should take a context describing which variables are in state and which are in row
        val rowVariable = ref.name.symbol != names.ComponentSymbol.INIT

        if (rowVariable)
          System.row(ref, sort)
        else
          System.state(ref, sort)

      case Exp.App(sort, prim, args : _*) =>
        val zeroS = System.pure(List[Terms.Term]())
        val argsS = args.foldLeft(zeroS) { case (collectS, arg) =>
          collectS.ap2(expr(context, arg)) { _ :+ _ }
        }

        argsS.map { argsT =>
          compound.funapp(prim.pprString, argsT : _*)
        }

