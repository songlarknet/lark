package lark.meta.smt

import lark.meta.base.num.Integer
import lark.meta.base.names
import lark.meta.base.pretty
import lark.meta.core.node.Node
import lark.meta.core.Prop.Judgment
import lark.meta.core.{Prop, Sort}
import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow, Prim, Val}

import lark.meta.smt.Solver
import lark.meta.smt.Term.compound
import lark.meta.smt.system
import lark.meta.smt.system.{System, SystemV, SystemJudgment, Namespace}
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import scala.collection.mutable

object Translate:

  case class Options(
    checkRefinement: Boolean = true
  )

  class Context(
    val nodes: Map[names.Ref, system.Node],
    val supply: names.mutable.Supply,
    val options: Options)

  class ExpContext(
    val context: Context,
    val node: Node):

    def supply = context.supply

  def nodes(inodes: Iterable[Node], options: Options): system.Top =
    var map = Map[names.Ref, system.Node]()
    val snodes = inodes.map { case inode =>
      val snode = node(new Context(map, new names.mutable.Supply(List()), options), inode)
      map += (inode.klass -> snode)
      snode
    }.toList
    system.Top(snodes, snodes.last)

  def node(context: Context, node: Node): system.Node =
    val sys        = nested(context, node, node.nested).system
    val params     = node.params.map { p => names.Ref.fromComponent(p) }.toList

    // We need to unbox each parameter with a bounded type to ensure that the
    // bounded integer constraints are added. Otherwise, the SMT translation
    // would allow out-of-range values for unused parameters, which can be
    // pretty confusing.
    val paramsS    = System.conjoin(node.params.map { p =>
      val x = node.xvar(p)
      x.sort match
        case s: Sort.Refinement =>
          expr(ExpContext(context, node), Exp.Cast(Exp.Cast.Unbox(s), x)).system
        case _ =>
          expr(ExpContext(context, node), x).system
    }.toSeq)

    def prop(judgment: Judgment): SystemJudgment =
      judgment.term match
        // LODO: deal with non-variables by creating a fresh row variable for them
        case Exp.Var(s, v) =>
          SystemJudgment(
            List(),
            v,
            judgment)

    val sysprops = System(
      relies     = node.relies.map(prop).toList,
      guarantees = node.guarantees.map(prop).toList,
      sorries    = node.sorries.map(prop).toList)

    system.Node(node.klass, params, sys <> paramsS <> sysprops)

  def nested(context: Context, node: Node, nested: Node.Nested): SystemV[Unit] =
    val contextPrefix = names.Prefix(List(nested.context))
    val children      = nested.children.map(binding(context, node, contextPrefix, _))

    val initR         = contextPrefix(names.Component(names.ComponentSymbol.INIT))
    val initS         =
      if nested.requiresInitFlag
      then
        for
          // init flag true initially
          initE <- SystemV.state(initR, Sort.Bool)
          _     <- SystemV.init(initE)
          // init flag false after step
          initX <- SystemV.stateX(initR, Sort.Bool)
          _     <- SystemV.step(compound.not(initX))
        yield ()
      else SystemV.pure(())

    initS <&& SystemV.conjoin(children.toSeq)

  def binding(context: Context, node: Node, contextPrefix: names.Prefix, binding: Node.Binding): SystemV[Unit] = binding match
    case b: Node.Binding.Equation =>
      val ec    = ExpContext(context, node)
      val xref  = names.Ref.fromComponent(b.lhs)
      val tstep =
        for
          erhs <- flow(ec, contextPrefix, b)
          x    <- SystemV.row(xref, b.rhs.sort)
        yield compound.equal(x, erhs)
      SystemV.step(tstep)

    case b: Node.Binding.Subnode =>
      val v = b.subnode
      val ec = ExpContext(context, node)
      val subnode = node.subnodes(v)
      val subsystem = context.nodes(subnode.klass)

      val argsT  = b.args.map(expr(ec, _))
      val argsEq: List[SystemV[Unit]] =
        subnode.params.zip(argsT).map { (param,argT) =>
          for
            argE  <- argT
            paramE = compound.qid(system.Prefix.row(names.Ref(List(v), param)))
            eq     = compound.equal(paramE, argE)
            _     <- SystemV.step(eq)
          yield ()
        }.toList

      def pfx(p: names.Prefix) = names.Prefix(p.prefix :+ v)
      def pfxR(r: names.Ref) = names.Ref(List(v) ++ r.prefix, r.name)
      def pfxJ(j: SystemJudgment) =
        SystemJudgment(j.hypotheses.map(pfxR), pfxR(j.consequent), j.judgment)

      val subrelies     = subsystem.system.relies.map(pfxJ)
      val subguarantees = subsystem.system.guarantees.map(pfxJ)
      val subsorries    = subsystem.system.sorries.map(pfxJ)
      // The subnode's assertions only hold if the rely preconditions are
      // always true, so we rewrite each assumption to `SoFar(/\ reqs) => asm`.
      // HACK: ignore the rely hypotheses. This is sound because we're
      // just making the assumption hypotheses stricter, but prove it or clean
      // it up.
      val addHypotheses = subrelies.map(_.consequent)
      // environment has to guarantee the subsystem's relies
      val guarantees = subrelies
      // environment can assume the subsytem's guarantees and sorries hold
      val sorries    =
        for j <- (subguarantees ++ subsorries)
        yield j.copy(hypotheses = j.hypotheses ++ addHypotheses)

      val subnodeT = System(
        state = names.Namespace.nest(v, subsystem.system.state),
        row   = names.Namespace.nest(v, subsystem.system.row),
        init  =
          val argsV = subsystem.initP(pfx(system.Prefix.state))
              .map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
          compound.funappNoSimp(subsystem.initI, argsV),
        step =
          val argsV = subsystem.stepP(pfx(system.Prefix.state), pfx(system.Prefix.row), pfx(system.Prefix.stateX))
              .map(v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)))
          compound.funappNoSimp(subsystem.stepI, argsV),
        relies     = List(),
        guarantees = guarantees,
        sorries    = sorries)

      SystemV(subnodeT, ()) <&& SystemV.conjoin(argsEq.toList)

    case b: Node.Binding.Merge =>
      def go(scrut: Terms.Term, case1: (Val, Node.Nested)): SystemV[Unit] =
        val whenE  = compound.equal(scrut, compound.value(case1._1))
        val subT   = nested(context, node, case1._2)
        subT.when(context.supply, whenE)
      for
        s <- expr(ExpContext(context, node), b.scrutinee)
        _ <- SystemV.conjoin(b.cases.map(go(s, _)))
      yield
        ()

    case b: Node.Binding.Reset =>
      val sub = nested(context, node, b.nested)
      for
        kE    <- expr(ExpContext(context, node), b.clock)
        // Put a copy of sub's state inside row.reset. There won't be
        // any conflicts because the nested contexts inside sub must have
        // unique ids.
        _     <- sub.reset(names.Component(names.ComponentSymbol.RESET), kE)
      yield ()

  /** Translate a streaming expression to a system. */
  def flow(context: ExpContext, contextPrefix: names.Prefix, b: Node.Binding.Equation): SystemV[Terms.Term] = b.rhs match
    case Flow.Pure(e) =>
      expr(context, e)

    case Flow.Arrow(first, later) =>
      val init = contextPrefix(names.Component(names.ComponentSymbol.INIT))
      for
        st  <- SystemV.state(init, Sort.Bool)
        fst <- expr(context, first)
        ltr <- expr(context, later)
      yield compound.ite(st, fst, ltr)

    case Flow.Pre(pre) =>
      val ref   = contextPrefix(b.lhs)
      val tstep =
        for
          v  <- expr(context, pre)
          st <- SystemV.stateX(ref, b.rhs.sort)
        yield compound.equal(st, v)

      SystemV.state(ref, b.rhs.sort) <&& SystemV.step(tstep)

    case Flow.Fby(v0, pre) =>
      val ref   = contextPrefix(b.lhs)
      val tinit =
        for
          st <- SystemV.state(ref, b.rhs.sort)
        yield compound.equal(st, compound.value(v0))
      val tstep =
        for
          v  <- expr(context, pre)
          st <- SystemV.stateX(ref, b.rhs.sort)
        yield compound.equal(st, v)

      SystemV.state(ref, b.rhs.sort) <&& SystemV.init(tinit) <&& SystemV.step(tstep)

  /** Translate a pure expression to a system. */
  def expr(context: ExpContext, exp: Exp): SystemV[Terms.Term] = exp match
    case Exp.Val(v) =>
      SystemV.pure(compound.value(v))

    case Exp.Var(sort, ref) =>
      // HACK: if the variable refers to the special ^state namespace, then
      // look up that variable in the state instead of the row.
      val stateVariable = (ref.prefix.exists(_.symbol == names.ComponentSymbol.STATE))

      if (stateVariable)
        SystemV.state(ref, sort)
      else
        SystemV.row(ref, sort)

    case Exp.App(sort, prim, args : _*) =>
      for
        targs <- SystemV.conjoin(args.map(expr(context, _)))
      yield compound.funapp(nameOfPrim(prim, sort), targs : _*)

    case Exp.Cast(_, e)
      if !context.context.options.checkRefinement
      => expr(context, e)

    // box(x : t) : { t | p }
    // requires   p(x);
    // guarantees \result.value == x;
    case Exp.Cast(Exp.Cast.Box(s), e) =>
      val relyR  = context.supply.freshRef(names.ComponentSymbol.PROP, forceIndex = true)
      val boxR   = context.supply.freshRef(names.ComponentSymbol.BOX, forceIndex = true)

      val relyJ = SystemJudgment(
        List(), relyR,
        Judgment(s"${s.pprString} bounds", s.refinesExp(e), Prop.Syntax.Generated.check, lark.meta.macros.Location.empty))

      for
        eT     <- expr(context, e)
        let    <- SystemV.letRow(s.logical, eT) { () =>
          context.supply.freshRef(names.ComponentSymbol.UNBOX, forceIndex = true)
        }
        ref  = let._1
        refT = let._2

        refV  = Exp.Var(s.logical, ref)
        relyT <- expr(context, s.refinesExp(refV))

        relyTX <- SystemV.row(relyR, Sort.Bool)
        boxT   <- SystemV.row(boxR, s.logical)

        _  <- SystemV.step(compound.equal(relyTX, relyT))
        _  <- SystemV.step(compound.implies(relyTX, compound.equal(refT, boxT)))

        _  <- SystemV(System(guarantees = List(relyJ)), ())
      yield
        boxT

    // unbox(x : { t | p }) : t
    // guarantees \result == x.value;
    // guarantees p(\result);
    case Exp.Cast(Exp.Cast.Unbox(logical), e) => e.sort match
      case refinement: Sort.Refinement =>
        for
          eT  <- expr(context, e)
          let <- SystemV.letRow(logical, eT) { () =>
            context.supply.freshRef(names.ComponentSymbol.UNBOX, forceIndex = true)
          }
          ref  = let._1
          refT = let._2

          refV  = Exp.Var(logical, ref)
          satT <- expr(context, refinement.refinesExp(refV))
          _    <- SystemV.step(satT)
        yield refT

      case _ =>
        assert(false, s"translate ${exp.pprString}: can't unbox sort ${logical.pprString} as it's not a refinement")


  def nameOfPrim(prim: Prim, sort: Sort): String = (prim, sort) match
    // Negate is printed as "-", but that conflicts with binary subtraction.
    case (term.prim.Table.Negate, _) => "-"
    // Use wrapper functions around division to make /0 safe.
    case (term.prim.Table.Div, Sort.Real) => "lark_div_Real"
    // SMT-PERF: when the numerator is nonnegative we could use lark_div_Nat
    // which is slightly simpler. Maybe we want to do a bounds analysis one day.
    case (term.prim.Table.Div, Sort.ArbitraryInteger) => "lark_div_Int"
    case _ => prim.pprString

