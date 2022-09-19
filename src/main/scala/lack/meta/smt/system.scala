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
import lack.meta.smt.term.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import scala.collection.mutable

object system:

  object Prefix:
    /** Namespace prefix for variables in starting state. */
    val state  = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("state"), None)))
    /** Namespace prefix for variables in successor (neXt) state. */
    val stateX = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("stateX"), None)))
    /** Namespace prefix for variables in row (non-state variables). */
    val row    = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("row"), None)))

  type Namespace = names.Namespace[Sort]

  /** A definition of a transition system in SMT-lib format.
   *
   * The main reason that this uses SMT-lib terms rather than core expressions
   * is that the systems need to be able to call init and step functions for
   * the subsystems, as well as defining local let bindings. It might be worth
   * defining a small core with these so that we can evaluate systems directly.
   *
   * @param state
   *  The types of the state variables used by the transition system. These
   *  variables describe the internal state of the system and aren't usually
   *  directly visible to the programmer.
   * @param row
   *  The "row" contains the types of all of the user-visible variables. This
   *  includes input variables that have no definition, as well as user-defined
   *  variables, and compiler-generated variables.
   *  We include input variables in here because it makes it a bit easier to
   *  compose systems together, and the SMT solver doesn't even really care
   *  whether a variable is an input or not. If we had a pipeline like:
   *  > f . g
   *  > where
   *  >  f(x) = x * 2
   *  >  g(y) = y + 1
   *  then the translation for the `f` node would have an input variable `x`
   *  but when we composed the two nodes it together, we'd have to make `x`
   *  a non-input.
   *  On the other hand, distinguishing between stateful variables and pure row
   *  variables is useful for, say, path compression.
   * @param init
   *  An SMT-lib term describing the set of allowed initial states. This term
   *  can refer to the state variables with the prefix Prefix.state. It should
   *  have sort Bool.
   * @param step
   *  An SMT-lib term describing the three-way relation between starting state,
   *  its row values (eg inputs and outputs), and the successor state. This
   *  term may refer to the state variables with prefix Prefix.state, the row
   *  variables with prefix Prefix.row, and the successor state variables with
   *  prefix Prefix.stateX. It should have sort Bool.
   * @param relies
   *  "Rely" properties that the environment must satisfy; these are checked
   *  in calling code. These are contract "requires".
   *  The properties here do *not* necessarily satisfy
   *  > `relies.forall(_.form == Form.Rely)`.
   *  as relies in subnodes become sorries for the caller.
   * @param guarantees
   *  "Guarantee" properties that we must prove that the system satisfies.
   *  These are proof obligations or contract "ensures".
   * @param sorries
   *  "Trusted" properties that everybody can assume to be true. These are
   *  assumed to be true in the body and the calling code.
   */
  case class System(
    state: Namespace  = names.Namespace(),
    row:   Namespace  = names.Namespace(),
    init:  Terms.Term = compound.bool(true),
    step:  Terms.Term = compound.bool(true),
    relies:     List[SystemJudgment] = List(),
    guarantees: List[SystemJudgment] = List(),
    sorries:    List[SystemJudgment] = List())
  extends pretty.Pretty:
    def ppr =
      pretty.subgroup("State:", List(state.ppr)) <>
      pretty.subgroup("Row:",   List(row.ppr)) <>
      pretty.subgroup("Init:",  List(pretty.string(term.pprTermBigAnd(init)))) <>
      pretty.subgroup("Step:",  List(pretty.string(term.pprTermBigAnd(step)))) <>
      pretty.subgroup("Relies:",     relies.map(_.ppr)) <>
      pretty.subgroup("Guarantees:", guarantees.map(_.ppr)) <>
      pretty.subgroup("Sorries:",    sorries.map(_.ppr))

    /** Parallel composition of systems. */
    def <>(that: System) = System(
      state = this.state <> that.state,
      row   = this.row <> that.row,
      init  = compound.and(this.init, that.init),
      step  = compound.and(this.step, that.step),
      relies     = this.relies ++ that.relies,
      guarantees = this.guarantees ++ that.guarantees,
      sorries    = this.sorries ++ that.sorries)

    /** Slow the clock of a system, so it only steps when the boolean
     * expression `klock` is true.
     */
    def when(klock: Terms.Term): System =
      val allSame =
        for s <- state.refs(names.Prefix(List()))
        yield compound.funapp("=",
          compound.qid(system.Prefix.state(s)),
          compound.qid(system.Prefix.stateX(s)))
      val stay = compound.and(allSame.toSeq : _*)

      System(
        state = this.state,
        row   = this.row,
        init  = this.init,
        step  = compound.ite(klock, this.step, stay),
        relies     = this.relies,
        guarantees = this.guarantees,
        sorries    = this.sorries)

    /** Reset a system whenever boolean expression `klock` is true.
     * Fresh is a fresh name such that row.fresh is not used.
     */
    def reset(fresh: names.Component, klock: Terms.Term): System =
      // We want to call the subsystem's step function with a starting state of
      // either the actual current state, or the initial state if we are
      // resetting.
      // To do this we allocate a fresh copy of the state, stateR, and call the
      // subsystem's step with step(stateR, row, stateX). When we are resetting
      // we set stateR to the initial state. When we are not resetting, we set
      // stateR to the starting state (`state`).

      // We really want to existentially quantify over the reset states, so
      // we sneak a version of the state into the row variables under 'fresh'.
      val nestStateN = names.Namespace.nest(fresh, this.state)
      val stateR     = names.Prefix(Prefix.row.prefix :+ fresh)

      // Substitute variable prefix `state` to refer to fresh prefix `stateR`.
      val initSubst  = term.renamePrefix(Prefix.state, stateR, this.init)
      val stepSubst  = term.renamePrefix(Prefix.state, stateR, this.step)

      val allSame    =
        for s <- state.refs(names.Prefix(List()))
        yield compound.funapp("=",
          compound.qid(Prefix.state(s)),
          compound.qid(stateR(s)))
      val noReset    = compound.and(allSame.toSeq : _*)
      val yeReset    = initSubst

      System(
        state = this.state,
        row   = this.row <> nestStateN,
        init  = this.init,
        step  = compound.and(
          compound.ite(klock, yeReset, noReset),
          stepSubst),
        relies     = this.relies,
        guarantees = this.guarantees,
        sorries    = this.sorries)


  object System:
    val empty: System = System()

    def state(ref: names.Ref, sort: Sort): System =
      System(state = names.Namespace.fromRef(ref, sort))

    def row(ref: names.Ref, sort: Sort): System =
      System(row = names.Namespace.fromRef(ref, sort))

    def conjoin(systems: Seq[System]): System =
      systems.fold(System.empty)(_ <> _)

    /** Add an assertion to the step relation.
     * The given term may refer to state variables prefixed by Prefix.state
     * or Prefix.stateX, or row variables prefixed by Prefix.row.
     * Any state or row variables should be declared separately with
     * System.state or System.row.
     */
    def step(term: Terms.Term): System =
      System(step = term)

    /** Add an assertion to the init predicate.
     * The given term may refer to state variables prefixed by Prefix.state.
     * State variables should be declared separately with System.state.
     */
    def init(term: Terms.Term): System =
      System(init = term)

  /** A transition system and some associated value.
   * The value could be an SMT-lib term that refers to state or row variables.
   */
  case class SystemV[T](system: System, value: T):
    def flatMap[U](f: T => SystemV[U]): SystemV[U] =
      val ts = f(value)
      SystemV(this.system <> ts.system, ts.value)

    def map[U](f: T => U): SystemV[U] =
      flatMap(t => SystemV.pure(f(t)))

    def when(klock: Terms.Term): SystemV[T] =
      SystemV(this.system.when(klock), this.value)

    def reset(fresh: names.Component, klock: Terms.Term): SystemV[T] =
      SystemV(this.system.reset(fresh, klock), this.value)

  object SystemV:
    def pure[T](value: T): SystemV[T] = SystemV(System.empty, value)

    def state(ref: names.Ref, sort: Sort): SystemV[Terms.Term] =
      SystemV(System.state(ref, sort), compound.qid(Prefix.state(ref)))

    def stateX(ref: names.Ref, sort: Sort): SystemV[Terms.Term] =
      SystemV(System.state(ref, sort), compound.qid(Prefix.stateX(ref)))

    def row(ref: names.Ref, sort: Sort): SystemV[Terms.Term] =
      SystemV(System.row(ref, sort), compound.qid(Prefix.row(ref)))

    def conjoin[T](systems: Seq[SystemV[T]]): SystemV[Seq[T]] =
      SystemV(System.conjoin(systems.map(_.system)), systems.map(_.value))

    def init(cond: Terms.Term): SystemV[Unit] =
      SystemV(System.init(cond), ())

    def init(cond: SystemV[Terms.Term]): SystemV[Unit] =
      for
        c <- cond
        _ <- init(c)
      yield ()

    def step(cond: Terms.Term): SystemV[Unit] =
      SystemV(System.step(cond), ())

    def step(cond: SystemV[Terms.Term]): SystemV[Unit] =
      for
        c <- cond
        _ <- step(c)
      yield ()

  extension[T,U] (outer: SystemV[T => U])
    /** Applicative functor for valued systems. */
    def <*>(that: SystemV[T]): SystemV[U] =
      for
        f <- outer
        t <- that
      yield f(t)

  extension[T] (outer: SystemV[T])
    /** Join two systems with given function. */
    def ap2[U, V](that: SystemV[U])(f: (T, U) => V): SystemV[V] =
      for
        u <- outer
        v <- that
      yield f(u, v)

    /** Join two systems, tupling the values together. */
    def <&>[U](that: SystemV[U]): SystemV[(T,U)] =
      ap2(that)((_,_))

    /** Join two systems, taking the first value as well as any constraints
     * and variable definitions from the second. */
    def <&&[U](that: SystemV[U]): SystemV[T] =
      ap2(that)((t,u) => t)

  /** A judgment with hypotheses.
   * The hypotheses and consequent refer to row variables excluding the row
   * prefix. All hypotheses must be true for current and previous steps:
   * > SoFar(row(hyps_0) and ... and row(hyps_i)) => row(consequent)
   *
   * This meaning is different from the bare implication `hyps => consequent`.
   */
  case class SystemJudgment(hypotheses: List[names.Ref], consequent: names.Ref, judgment: Judgment) extends pretty.Pretty:
    def ppr =
      val hyp = hypotheses match
        case Nil => pretty.emptyDoc
        case hs  => pretty.text("SoFar") <>
          pretty.parens(pretty.ssep(hs.map(_.ppr), pretty.text(" and "))) <>
          pretty.text(" => ")

      pretty.value(judgment.form) <>
        pretty.parens(pretty.value(judgment.name)) <+>
        pretty.equal <+>
        hyp <> consequent.ppr

  /** A system for a node */
  case class Node(
    path: List[names.Component],
    params: List[names.Ref],
    system: System
  ) extends pretty.Pretty:
    def ppr =
      pretty.text("Node") <+> names.Prefix(path).ppr <>
        pretty.parens(pretty.csep(params.map(_.ppr))) <>
        pretty.nest(pretty.line <> system.ppr)

    /** Convert namespace to list of SMT-lib parameters */
    def paramsOfNamespace(prefix: names.Prefix, ns: Namespace): List[Terms.SortedVar] =
      val vs = ns.values.toList.map((v,s) => Terms.SortedVar(compound.qid(prefix(names.Ref(List(), v))).id.symbol, translate.sort(s)))
      val nsX = ns.namespaces.toList.flatMap((v,n) => paramsOfNamespace(names.Prefix(prefix.prefix :+ v), n))
      vs ++ nsX

    private def nm(i: String): names.Ref =
      names.Ref(path, names.Component(names.ComponentSymbol.fromScalaSymbol(i), None))

    /** Qualified identifier of init function. */
    val initI      = compound.qid(nm("init"))
    /** Qualified identifier of step function. */
    val stepI      = compound.qid(nm("step"))

    /** Parameters for init function. */
    def initP(state: names.Prefix): List[Terms.SortedVar] =
      paramsOfNamespace(state, system.state)

    /** Parameters for step function. */
    def stepP(state: names.Prefix, row: names.Prefix, stateX: names.Prefix): List[Terms.SortedVar] =
      paramsOfNamespace(state,  system.state) ++
      paramsOfNamespace(row,    system.row) ++
      paramsOfNamespace(stateX, system.state)

    /** Function definition for init function. */
    val initD = Commands.FunDef(
      initI.id.symbol,
      initP(Prefix.state),
      translate.sort(Sort.Bool),
      system.init)
    /** Function definition for step function. */
    val stepD = Commands.FunDef(
      stepI.id.symbol,
      stepP(Prefix.state, Prefix.row, Prefix.stateX),
      translate.sort(Sort.Bool),
      system.step)

    /** Function definition for step function. */
    def fundefs: List[Commands.DefineFun] =
      List(Commands.DefineFun(initD), Commands.DefineFun(stepD))

  /** A top-level system with subnodes. */
  case class Top(nodes: List[Node], top: Node) extends pretty.Pretty:
    def fundefs: List[Commands.DefineFun] = nodes.flatMap(_.fundefs)

    def ppr = pretty.vsep(nodes.map(_.ppr))
