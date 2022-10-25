package lark.meta.smt

import lark.meta.base.names
import lark.meta.core.node.Node
import smtlib.trees.{Commands, CommandsResponses, Terms}

/** Get the SMT solver to evaluate a node. */
object Eval:

  /** Generate a bunch of traces from the SMT solver.
   *
   * This just asks the SMT solver to return traces of increasing length. There
   * are no constraints to ask for "interesting" traces. In practice Z3 does
   * seem to choose values that reach different states, but there isn't much
   * variation. A lot of the values are zero, so I wonder whether there's a
   * sort of soft constraint that tries to bring them down to zero.
   *
   * LODO: generate more interesting traces. One idea might be to generate a
   * random value for each input argument, and constrain them with soft
   * assertions. We could also add soft assertions that the states should be
   * distinct. Z3 supports soft assertions, but I don't think CVC5 does.
   */
  def generate(top: Node, solver: Solver, options: Translate.Options = Translate.Options()): Stream[Trace] =
    val sys  = Prove.declareSystem(top, solver, options)
    val topS = sys.top

    {
      val state = topS.paramsOfNamespace(Prove.statePrefix(0), topS.system.state)
      solver.declareConsts(state)
      Prove.callSystemFun(topS.initI, state, solver)
    }

    Stream.from(0).map { step =>
      val state  = topS.paramsOfNamespace(Prove.statePrefix(step), topS.system.state)
      val stateS = topS.paramsOfNamespace(Prove.statePrefix(step + 1), topS.system.state)
      val row    = topS.paramsOfNamespace(Prove.rowPrefix(step), topS.system.row)

      solver.declareConsts(row ++ stateS)

      Prove.callSystemFun(topS.stepI, state ++ row ++ stateS, solver)

      Prove.asserts(topS.system.relies, step, solver)
      Prove.asserts(topS.system.sorries, step, solver)

      val sat = solver.checkSat()
      sat.status match
        case CommandsResponses.SatStatus =>
          val model = solver.command(Commands.GetModel())
          Trace.fromModel(step, model)
        case _ =>
          throw new Exception(
            s"""Can't generate trace for node ${top.klass.pprString}:
               |  Response: ${sat}
               |  Step: ${step}""".stripMargin)
    }
