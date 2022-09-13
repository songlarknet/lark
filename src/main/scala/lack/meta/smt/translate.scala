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
import lack.meta.smt.system.{System, SolverNode, SolverSystem, SolverFunDef, SolverJudgment, Namespace}
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import scala.collection.mutable

object translate:

  def sort(s: Sort): Terms.Sort = s match
    case _: Sort.Integral => Terms.Sort(compound.id("Int"))
    case _: Sort.Mod => Terms.Sort(compound.id("Int"))
    case Sort.Float32 => Terms.Sort(compound.id("Float !TODO"))
    case Sort.Real32 => Terms.Sort(compound.id("Real"))
    case Sort.Bool => Terms.Sort(compound.id("Bool"))

  def value(v: Val): Terms.Term = v match
    case Val.Bool(b) => compound.qid(b.toString)
    case Val.Int(i) => compound.int(i)
    case Val.Real32(f) => compound.real(f)

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

    val initT      = sys.init(system.Prefix.state)
    val (stepT, _) = sys.step(system.Prefix.state, system.Prefix.row, system.Prefix.stateX)

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
      require(!(sort.isInstanceOf[Sort.Mod] && prim.isInstanceOf[Prim.Div.type]),
        "TODO: division for bitvectors has weird semantics in SMT-lib, need to wrap division to get consistent div-by-zero behaviour")

      val zeroS = System.pure(List[Terms.Term]())
      val argsS = args.foldLeft(zeroS) { case (collectS, arg) =>
        collectS.ap2(expr(context, arg)) { _ :+ _ }
      }

      argsS.map { argsT =>
        compound.funapp(prim.pprString, argsT : _*)
      }

