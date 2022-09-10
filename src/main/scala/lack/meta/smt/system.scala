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
    val state  = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("state"), None)))
    val stateX = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("stateX"), None)))
    val row    = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("row"), None)))

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
