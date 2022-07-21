package lack.meta.smt

import lack.meta.base.Integer
import lack.meta.core.builder.Node
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val, Var}

import lack.meta.smt.solver.Solver
import lack.meta.smt.solver.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

object check:
  /** The pretty-printer needs to know whether a step is the initial step or
    * the next step.
    */
  sealed trait StepType
  object StepType:
    /** Initial state. (x -> y) is printed as x. */
    case object Init extends StepType
    /** Non-reset transition. (x -> y) is printed as y. */
    case object Transition extends StepType
    /** Abstract state before a transition.
      * This is used as the start of evaluation for the inductive case.
      * (x -> y) could evaluate to either x or y. */
    case object Free extends StepType

  sealed trait CheckFeasible
  object CheckFeasible:
    case object Feasible extends CheckFeasible
    case object Infeasible extends CheckFeasible


  sealed trait Bmc
  object Bmc:
    case class Counterexample(steps: Int, expr: SExpr) extends Bmc
    case class SafeUpTo(steps: Int) extends Bmc
    case class Unknown(steps: Int) extends Bmc

  sealed trait Kind
  object Kind:
    case class InvariantAt(steps: Int) extends Kind
    case class NoGood(steps: Int) extends Kind


  def feasible(n: Node, count: Int, solver: Solver): Option[CheckFeasible] =
    val steps = (0 until count).map { i => new Stepped(i, if (i == 0) StepType.Init else StepType.Transition) }
    steps.foreach { step =>
      step.nodedeclares(n, solver)
      step.nodebinds(n, solver)
    }
    solver.checkSat().status match
      case CommandsResponses.UnknownStatus => None
      case CommandsResponses.SatStatus     => Some(CheckFeasible.Feasible)
      case CommandsResponses.UnsatStatus   => Some(CheckFeasible.Infeasible)

  def bmc(n: Node, count: Int, solver: Solver): Bmc =
    solver.command(Commands.SetOption(Commands.ProduceModels(true)))

    val steps = (0 until count).map { i => new Stepped(i, if (i == 0) StepType.Init else StepType.Transition) }
    steps.foreach { step =>
      step.nodedeclares(n, solver)
      step.nodebinds(n, solver)
      val xcounterexample = compound.funapp("or", n.allPropObligations.map(p => compound.funapp("not", step.ppexp(p.term))) : _*)
      solver.checkSatAssumingX(xcounterexample) { _.status match
        case CommandsResponses.UnknownStatus => return Bmc.Unknown(step.step)
        case CommandsResponses.SatStatus     =>
          val model = solver.command(Commands.GetAssignment())
          // solver.command(Commands.GetValue(step.ppexp(n.subnodes.head.bindings.head._1), Seq()))
          return Bmc.Counterexample(step.step, model)
        case CommandsResponses.UnsatStatus   =>
      }
    }
    Bmc.SafeUpTo(count)

  def kind(n: Node, count: Int, solver: Solver): Kind =
    val steps = (0 to count).map { i => new Stepped(i, if (i == 0) StepType.Free else StepType.Transition) }
    steps.foreach { step =>
      step.nodedeclares(n, solver)
      step.nodebinds(n, solver)
      val ands = compound.funapp("and", n.allPropObligations.map(p => step.ppexp(p.term)) : _*)
      if (step.step == 0)
        solver.assert(ands)
      else
        val xcounterexample = compound.funapp("or", n.allPropObligations.map(p => compound.funapp("not", step.ppexp(p.term))) : _*)
        solver.checkSatAssumingX(xcounterexample) { res =>
          if (res.status == CommandsResponses.UnsatStatus)
            return Kind.InvariantAt(step.step)
        }
        solver.assert(ands)
    }
    Kind.NoGood(count)


  class Stepped(val step: Int, val ty: StepType):

    def ppvar(v: Var): Terms.SSymbol =
      compound.sym(s"${v.pretty}@${step}")

    def ppsort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def ppval(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => Terms.SNumeral(i)
      // TODO

    def ppexp(e: Exp): Terms.Term = e match
      case Exp.flow.Arrow(first, later) => ty match
        case StepType.Init => ppexp(first)
        case StepType.Transition => ppexp(later)
        case StepType.Free => throw new Exception(s"can't pretty-print expression (x -> y) for StepType.Free ${e}")
      case Exp.flow.Pre(pre) => ty match
        case StepType.Init => throw new Exception(s"can't pretty-print expression (pre e) for StepType.Init ${e}")
        case StepType.Transition => new Stepped(step - 1, ty).ppexp(pre)
        case StepType.Free => throw new Exception(s"can't pretty-print expression (pre e) for StepType.Free ${e}")
      case Exp.Val(v) => ppval(v)
      case Exp.Var(v) => Terms.QualifiedIdentifier(Terms.Identifier(ppvar(v)))
      case Exp.App(prim, args : _*) =>
        compound.funapp(prim.pretty, args.map(ppexp(_)) : _*)

    def declares(vs: List[Var], solver: Solver): Unit =
      vs.foreach { v =>
        solver.declareConst(ppvar(v), ppsort(v.sort))
      }

    def bind(lhs: Exp, rhs: Exp, solver: Solver): Unit = rhs match
      case Exp.flow.Arrow(first, later)
        if ty == StepType.Free =>
          solver.assert(
            compound.funapp("or",
              compound.funapp("=", ppexp(lhs), ppexp(first)),
              compound.funapp("=", ppexp(lhs), ppexp(later))))
      case Exp.flow.Pre(pre)
        if ty == StepType.Init =>
          // unguarded pre for init (step 0)
      case Exp.flow.Pre(pre)
        if ty == StepType.Free =>
          // unguarded pre for free (pre-transition)
      case _ =>
        solver.assert(
          compound.funapp("=", ppexp(lhs), ppexp(rhs)))

    def nodedeclares(n: Node, solver: Solver): Unit =
      declares(n.vars, solver)
      n.subnodes.foreach { nx =>
        nodedeclares(nx, solver)
      }

    def nodebinds(n: Node, solver: Solver): Unit =
      n.bindings.foreach { case (l,r) =>
        bind(l, r, solver)
      }
      n.subnodes.foreach { nx =>
        nodebinds(nx, solver)
      }

