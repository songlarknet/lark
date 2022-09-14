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
import lack.meta.smt.system
import lack.meta.smt.system.{System, SystemV, SystemJudgment, Namespace}
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

  class Context(val nodes: Map[List[names.Component], system.Node], val supply: names.mutable.Supply)

  class ExpContext(val node: Node, val init: names.Ref, val supply: names.mutable.Supply):
    def stripRef(r: names.Ref): names.Ref =
      ExpContext.stripRef(node, r)

  object ExpContext:
    def stripRef(node: Node, r: names.Ref): names.Ref =
      val pfx = node.path
      require(r.prefix.startsWith(pfx),
        s"Ill-formed node in node ${names.Prefix(node.path).pprString}: all variable references should start with the node's path, but ${r.pprString} doesn't")
      val strip = r.prefix.drop(pfx.length)
      names.Ref(strip, r.name)

  def nodes(inodes: Iterable[Node]): system.Top =
    var map = Map[List[names.Component], system.Node]()
    val snodes = inodes.map { case inode =>
      val snode = node(new Context(map, new names.mutable.Supply(List())), inode)
      map += (inode.path -> snode)
      snode
    }.toList
    system.Top(snodes, snodes.last)

  def node(context: Context, node: Node): system.Node =
    def nm(i: names.ComponentSymbol): names.Ref =
      names.Ref(node.path, names.Component(i, None))

    val sys        = nested(context, node, None, node.nested).system
    val params     = node.params.map { p => names.Ref(List(), p) }.toList

    def prop(judgment: Judgment): SystemJudgment =
      judgment.term match
        // LODO: deal with non-variables by creating a fresh row variable for them
        case Exp.Var(s, v) =>
          SystemJudgment(List(), ExpContext.stripRef(node, v), judgment)

    val (obligations, assumptions) =
      node.props.toList.map(prop).partition(j => j.judgment.isObligation)
    val sysprops = System(obligations = obligations, assumptions = assumptions)

    system.Node(node.path, params, sys <> sysprops)

  def nested(context: Context, node: Node, init: Option[names.Ref], nested: builder.Binding.Nested): SystemV[Unit] =
    nested.selector match
    case builder.Selector.When(k) =>
      val initR    = names.Ref(List(), nested.init)
      val children = nested.children.map(binding(context, node, initR, _))

      val tk = init match
        case None =>
          // Blah - restructure, top level needs const clock so init=None
          require(k == Exp.Val(Sort.Bool, Val.Bool(true)))
          SystemV.pure(compound.bool(true))
        case Some(i) =>
          // Evaluate clock in parent init context
          expr(ExpContext(node, i, context.supply), k)

      val tstep =
        for
          initX <- SystemV.stateX(initR, Sort.Bool)
          _     <- SystemV.step(compound.funapp("not", initX))
          _     <- SystemV.conjoin(children.toSeq)
        yield ()

      for
        initE <- SystemV.state(initR, Sort.Bool)
        kE    <- tk
        _     <- SystemV.init(initE)
        _     <- tstep.when(kE)
      yield ()

    case builder.Selector.Reset(k) =>
      val initR    = names.Ref(List(), nested.init)
      val children = nested.children.map(binding(context, node, initR, _))

      val tk = init match
        case None =>
          assert(false,
            s"builder.Node invariant failure: top-level nested needs to be a when(true). Node ${names.Prefix(node.path).pprString}")
        case Some(i) =>
          // Evaluate clock in parent init context
          expr(ExpContext(node, i, context.supply), k)

      val tstep =
        for
          initX <- SystemV.stateX(initR, Sort.Bool)
          _     <- SystemV.step(compound.funapp("not", initX))
          _     <- SystemV.conjoin(children.toSeq)
        yield ()

      for
        initE <- SystemV.state(initR, Sort.Bool)
        kE    <- tk
        _     <- SystemV.init(initE)
        _     <- tstep.reset(nested.init, kE)
      yield ()

  def binding(context: Context, node: Node, init: names.Ref, binding: builder.Binding): SystemV[Unit] = binding match
    case builder.Binding.Equation(lhs, rhs) =>
      val ec    = ExpContext(node, init, context.supply)
      val xbind = node.xvar(lhs)
      val xref  = names.Ref(List(), lhs)
      val tstep =
        for
          erhs <- expr(ec, rhs)
          x    <- SystemV.row(xref, xbind.sort)
        yield compound.funapp("=", erhs, x)
      SystemV.step(tstep)

    case builder.Binding.Subnode(v, args) =>
      val ec = ExpContext(node, init, context.supply)
      val subnode = node.subnodes(v)
      val subsystem = context.nodes(subnode.path)

      val argsT  = args.map(expr(ec, _))
      val argsEq: List[SystemV[Unit]] =
        subnode.params.zip(argsT).map { (param,argT) =>
          for
            argE  <- argT
            paramE = compound.qid(system.Prefix.row(names.Ref(List(v), param)))
            eq     = compound.funapp("=", paramE, argE)
            _     <- SystemV.step(eq)
          yield ()
        }.toList

      def pfx(p: names.Prefix) = names.Prefix(p.prefix :+ v)

      // Get all of the subnode's judgments. Contract requires become
      // obligations at the use-site. Other judgments become assumptions
      // here as they've been proven in the subnode itself.
      // Should all local properties bubble up? What about sorries?
      // TODO: UNSOUND: rewrite assumptions to sofar(/\ reqs) => asms. This shouldn't matter for nodes without contracts.
      // TODO: TOMORROW: check rewrite ok
      def pfxR(r: names.Ref): names.Ref = names.Ref(List(v) ++ r.prefix, r.name)
      val subjudg =
        for j <- subsystem.system.assumptions ++ subsystem.system.obligations
        yield SystemJudgment(j.hypotheses.map(pfxR), pfxR(j.consequent), j.judgment)
      val (reqs, asms) = subjudg.partition(j => j.judgment.form == lack.meta.core.prop.Form.Require)

      val subnodeT = System(
        state = names.Namespace.nest(v, subsystem.system.state),
        row   = names.Namespace.nest(v, subsystem.system.row),
        init  =
          val argsV = subsystem.initP(pfx(system.Prefix.state))
              .map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
          Terms.FunctionApplication(subsystem.initI, argsV),
        step =
          val argsV = subsystem.stepP(pfx(system.Prefix.state), pfx(system.Prefix.row), pfx(system.Prefix.stateX))
              .map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
          Terms.FunctionApplication(subsystem.stepI, argsV),
        assumptions = asms,
        obligations = reqs.map(j => j.copy(judgment = j.judgment.copy(form = lack.meta.core.prop.Form.SubnodeRequire))))

      SystemV(subnodeT, ()) <&& SystemV.conjoin(argsEq.toList)

    case nest: builder.Binding.Nested =>
      nested(context, node, Some(init), nest)

  /** Translate a streaming expression to a system. */
  def expr(context: ExpContext, exp: Exp): SystemV[Terms.Term] = exp match
    case Exp.flow.Arrow(_, first, later) =>
      for
        st  <- SystemV.state(context.init, Sort.Bool)
        fst <- expr(context, first)
        ltr <- expr(context, later)
      yield compound.ite(st, fst, ltr)

    case Exp.flow.Pre(sort, pre) =>
      val ref   = context.supply.freshRef(names.ComponentSymbol.FBY, forceIndex = true)
      val tstep =
        for
          v  <- expr(context, pre)
          st <- SystemV.stateX(ref, sort)
        yield compound.funapp("=", st, v)

      SystemV.state(ref, sort) <&& SystemV.step(tstep)

    case Exp.flow.Fby(sort, v0, pre) =>
      val ref   = context.supply.freshRef(names.ComponentSymbol.FBY, forceIndex = true)
      val tinit =
        for
          st <- SystemV.state(ref, sort)
        yield compound.funapp("=", st, value(v0))
      val tstep =
        for
          v  <- expr(context, pre)
          st <- SystemV.stateX(ref, sort)
        yield compound.funapp("=", st, v)

      SystemV.state(ref, sort) <&& SystemV.init(tinit) <&& SystemV.step(tstep)

    case Exp.Val(_, v) =>
      SystemV.pure(value(v))

    case Exp.Var(sort, v) =>
      val ref = context.stripRef(v)
      // TODO HACK: should take a context describing which variables are in state and which are in row
      val rowVariable = ref.name.symbol != names.ComponentSymbol.INIT

      if (rowVariable)
        SystemV.row(ref, sort)
      else
        SystemV.state(ref, sort)

    case Exp.App(sort, prim, args : _*) =>
      require(!(sort.isInstanceOf[Sort.Mod] && prim.isInstanceOf[Prim.Div.type]),
        "TODO: division for bitvectors has weird semantics in SMT-lib, need to wrap division to get consistent div-by-zero behaviour")

      for
        targs <- SystemV.conjoin(args.map(expr(context, _)))
      yield compound.funapp(prim.pprString, targs : _*)
