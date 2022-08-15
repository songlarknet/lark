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

object check:
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
    val steps = (0 until count).map { i => new Stepped(i) }
    steps.foreach { step =>
      step.nodedeclares(n, solver)
      step.nodebinds(n, solver)
    }
    solver.checkSat().status match
      case CommandsResponses.UnknownStatus => None
      case CommandsResponses.SatStatus     => Some(CheckFeasible.Feasible)
      case CommandsResponses.UnsatStatus   => Some(CheckFeasible.Infeasible)

  def bmc(n: Node, count: Int, solver: Solver): Bmc =
    // solver.command(Commands.SetOption(Commands.ProduceModels(true)))

    // val steps = (0 until count).map { i => new Stepped(i) }
    // steps.foreach { step =>
    //   step.nodedeclares(n, solver)
    //   step.nodebinds(n, solver)
    //   val xcounterexample = compound.funapp("or", n.allPropObligations.map(p => compound.funapp("not", step.ppexp(p.term))).toSeq : _*)
    //   solver.checkSatAssumingX(xcounterexample) { _.status match
    //     case CommandsResponses.UnknownStatus => return Bmc.Unknown(step.step)
    //     case CommandsResponses.SatStatus     =>
    //       val model = solver.command(Commands.GetAssignment())
    //       // solver.command(Commands.GetValue(step.ppexp(n.subnodes.head.bindings.head._1), Seq()))
    //       return Bmc.Counterexample(step.step, model)
    //     case CommandsResponses.UnsatStatus   =>
    //   }
    // }
    Bmc.SafeUpTo(count)

  def kind(n: Node, count: Int, solver: Solver): Kind =
    // val steps = (0 to count).map { i => new Stepped(i) }
    // steps.foreach { step =>
    //   step.nodedeclares(n, solver)
    //   step.nodebinds(n, solver)
    //   val ands = compound.funapp("and", n.allPropObligations.map(p => step.ppexp(p.term)).toSeq : _*)
    //   if (step.step == 0)
    //     solver.assert(ands)
    //   else
    //     val xcounterexample = compound.funapp("or", n.allPropObligations.map(p => compound.funapp("not", step.ppexp(p.term))).toSeq : _*)
    //     solver.checkSatAssumingX(xcounterexample) { res =>
    //       if (res.status == CommandsResponses.UnsatStatus)
    //         return Kind.InvariantAt(step.step)
    //     }
    //     solver.assert(ands)
    // }
    Kind.NoGood(count)


  class Stepped(val step: Int):

    def ppref(v: lack.meta.core.names.Ref): Terms.SSymbol =
      compound.sym(s"${v.pretty}@${step}")

    def ppsort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def ppval(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => compound.int(i)
      // TODO


    // def declares(path: List[names.Component], vs: List[(names.Component, builder.Variable)], solver: Solver): Unit =
    //   vs.foreach { v =>
    //     solver.declareConst(ppref(names.Ref(path, v._1)), ppsort(v._2.sort))
    //   }

    // def bind(lhs: Exp, rhs: Exp, solver: Solver): Unit = rhs match
    //   case Exp.flow.Arrow(first, later)
    //     if ty == StepType.Free =>
    //       solver.assert(
    //         compound.funapp("or",
    //           compound.funapp("=", ppexp(lhs), ppexp(first)),
    //           compound.funapp("=", ppexp(lhs), ppexp(later))))
    //   case Exp.flow.Pre(pre)
    //     if ty == StepType.Init =>
    //       // unguarded pre for init (step 0)
    //   case Exp.flow.Pre(pre)
    //     if ty == StepType.Free =>
    //       // unguarded pre for free (pre-transition)
    //   case _ =>
    //     solver.assert(
    //       compound.funapp("=", ppexp(lhs), ppexp(rhs)))

    def nodedeclares(n: Node, solver: Solver): Unit = {}
    //   declares(n.path, n.vars.toList, solver)
    //   n.subnodes.foreach { nx =>
    //     nodedeclares(nx._2, solver)
    //   }

    def nodebinds(n: Node, solver: Solver): Unit = {}
      // TODO
      // n.bindings.foreach { case (l,r) =>
      //   bind(l, r, solver)
      // }
      // n.subnodes.foreach { nx =>
      //   nodebinds(nx, solver)
      // }

