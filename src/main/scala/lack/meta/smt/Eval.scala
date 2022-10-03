package lack.meta.smt

import lack.meta.base.names
import lack.meta.core.node.Builder.Node
import smtlib.trees.{Commands, CommandsResponses, Terms}

/** Get the SMT solver to evaluate a node. */
object Eval:

  /** Generate a bunch of traces */
  def generate(top: Node, solver: Solver, options: Translate.Options = Translate.Options()): Stream[Trace] =
    val sys  = Check.declareSystem(top, solver, options)
    val topS = sys.top

    {
      val state = topS.paramsOfNamespace(Check.statePrefix(0), topS.system.state)
      solver.declareConsts(state)
      Check.callSystemFun(topS.initI, state, solver)
    }

    Stream.from(0).map { step =>
      val state  = topS.paramsOfNamespace(Check.statePrefix(step), topS.system.state)
      val stateS = topS.paramsOfNamespace(Check.statePrefix(step + 1), topS.system.state)
      val row    = topS.paramsOfNamespace(Check.rowPrefix(step), topS.system.row)

      solver.declareConsts(row ++ stateS)

      Check.callSystemFun(topS.stepI, state ++ row ++ stateS, solver)

      Check.asserts(topS.system.relies, step, solver)
      Check.asserts(topS.system.sorries, step, solver)

      val sat = solver.checkSat()
      sat.status match
        case CommandsResponses.SatStatus =>
          val model = solver.command(Commands.GetModel())
          Trace.fromModel(step, model)
        case _ =>
          throw new Exception(
            s"""Can't generate trace for node ${names.Prefix(top.path).pprString}:
               |  Response: ${sat}
               |  Step: ${step}""".stripMargin)
    }
