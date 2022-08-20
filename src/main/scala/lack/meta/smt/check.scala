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
    case class FeasibleUpTo(steps: Int) extends CheckFeasible
    case class InfeasibleAt(steps: Int) extends CheckFeasible
    case class UnknownAt(steps: Int) extends CheckFeasible


  sealed trait Bmc
  object Bmc:
    case class Counterexample(steps: Int, expr: SExpr) extends Bmc
    case class SafeUpTo(steps: Int) extends Bmc
    case class Unknown(steps: Int) extends Bmc

  sealed trait Kind
  object Kind:
    case class InvariantAt(steps: Int) extends Kind
    case class NoGood(steps: Int) extends Kind

  def declareSystem(n: Node, solver: Solver): system.SolverSystem =
    val sys = system.translate.nodes(n.allNodes)
    sys.fundefs.foreach(solver.command)
    sys

  def stepPrefix(pfx: String, i: Int) = system.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol(pfx), Some(i))))
  def statePrefix(i: Int) = stepPrefix("state", i)
  def rowPrefix(i: Int) = stepPrefix("row", i)
  def initOraclePrefix = stepPrefix("init-oracle", 0)
  def stepOraclePrefix(i: Int) = stepPrefix("step-oracle", i)

  def callSystemFun(fun: system.SolverFunDef, argVars: List[Terms.SortedVar], oraclePrefix: system.Prefix, solver: Solver): Unit =
    val oracles = fun.oracles.map { (v,s) =>
      Terms.SortedVar(compound.sym(oraclePrefix.pfx + "/" + v.name), system.translate.sort(s))
    }
    solver.declareConsts(oracles)

    val argsV = argVars ++ oracles
    val argsT = argsV.map { v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)) }
    val call = Terms.FunctionApplication(fun.name, argsT)
    solver.assert(call)

  def feasible(n: Node, count: Int, solver: Solver): CheckFeasible =
    val sys = declareSystem(n, solver)
    val top = sys.top

    {
      val state = top.paramsOfNamespace(statePrefix(0), top.state)
      solver.declareConsts(state)
      callSystemFun(top.init, state, initOraclePrefix, solver)
    }

    solver.checkSat().status match
      case CommandsResponses.UnknownStatus => return CheckFeasible.UnknownAt(-1)
      case CommandsResponses.SatStatus     =>
      case CommandsResponses.UnsatStatus   => return CheckFeasible.InfeasibleAt(-1)

    for (step <- 0 until count) {
      val state  = top.paramsOfNamespace(statePrefix(step), top.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.step, state ++ row ++ stateS, stepOraclePrefix(step), solver)

      solver.checkSat().status match
        case CommandsResponses.UnknownStatus => return CheckFeasible.UnknownAt(-1)
        case CommandsResponses.SatStatus     =>
        case CommandsResponses.UnsatStatus   => return CheckFeasible.InfeasibleAt(-1)
    }

    CheckFeasible.FeasibleUpTo(count)

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
