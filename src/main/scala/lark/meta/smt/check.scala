package lark.meta.smt

import lark.meta.base.names
import lark.meta.base.pretty
import lark.meta.core.node.Builder.Node

import lark.meta.smt.Term.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext
import scala.concurrent.Await
import scala.concurrent.duration.Duration

object Check:

  case class Options(
    solver:                  () => Solver = { () => Solver.gimme(verbose = false) },
    translate:               Translate.Options = Translate.Options(),
    maximumInductiveSteps:   Int = 5,
    requireFeasibilitySteps: Int = 5,
  )

  sealed trait CheckFeasible extends pretty.Pretty
  object CheckFeasible:
    case class FeasibleUpTo(steps: Int) extends CheckFeasible:
      def ppr = pretty.text(s"Feasible (no contradictory assumptions) up to ${steps} steps")
    case class InfeasibleAt(steps: Int) extends CheckFeasible:
      def ppr = pretty.text(s"Infeasible at ${steps} steps")
    case class UnknownAt(steps: Int) extends CheckFeasible:
      def ppr = pretty.text(s"Unknown (at step ${steps})")


  sealed trait Bmc extends pretty.Pretty
  object Bmc:
    case class SafeUpTo(steps: Int) extends Bmc:
      def ppr = pretty.text(s"Safe for at least ${steps} steps")
    case class CounterexampleAt(steps: Int, trace: Trace) extends Bmc:
      def ppr = pretty.text("Counterexample with") <+> pretty.value(steps + 1) <+> "steps" <> pretty.colon <> pretty.nest(pretty.line <> trace.pprTruncate())
    case class UnknownAt(steps: Int) extends Bmc:
      def ppr = pretty.text(s"Unknown (at step ${steps})")


  sealed trait Kind extends pretty.Pretty
  object Kind:
    case class InvariantMaintainedAt(steps: Int) extends Kind:
      def ppr = pretty.text(s"Invariant maintained with ${steps} steps")
    case class NoGood(steps: Int, traces: List[Trace]) extends Kind:
      def ppr = pretty.text(s"Inductive step failed after trying up to ${steps} steps.") <>
        pretty.nest(traces match
          // Print the 1-inductive counterexample-to-induction if possible, as
          // it's the shortest that might hint to the user what's missing.
          case _ :: cti1 :: _ =>
            pretty.line <> pretty.text("1-inductive counterexample:") <@> cti1.pprTruncate()
          case cti0 :: _ =>
            pretty.line <> pretty.text("0-inductive counterexample:") <@> cti0.pprTruncate()
          case _ =>
            pretty.line <> pretty.text("(counterexample unavailable)"))
    case class UnknownAt(steps: Int) extends Kind:
      def ppr = pretty.text(s"Unknown (at step ${steps})")

  case class Summary(results: List[NodeSummary]) extends pretty.Pretty:
    val ok = results.forall(_.ok)
    def ppr =
      val nok = results.count(!_.ok)
      if (ok)
        pretty.text(s"OK: ${results.length} nodes ok")
      else
        pretty.text(s"NOK: ${nok}/${results.length} nodes failed")

    /** True if any nodes required induction */
    val nontrivial =
      results.exists(n => n.ok && !n.trivial)

  sealed trait NodeSummary(node: Node, val ok: Boolean, val trivial: Boolean = true) extends pretty.Pretty
  object NodeSummary:
    case class Skip(node: Node) extends NodeSummary(node, true):
      def ppr = pretty.text("Skipping node") <+> names.Prefix(node.path).ppr <> ", nothing to prove"

    case class OK(node: Node, steps: Int) extends NodeSummary(node, ok = true, trivial = steps == 0):
      def ppr = pretty.text(s"OK! (requires ${steps} inductive steps)")

    case class Infeasible(node: Node, details: CheckFeasible) extends NodeSummary(node, false):
      def ppr =
        pretty.text("Properties hold, but system is infeasible.") <@>
        pretty.text("Maybe you have inconsistent assumptions or contradictory definitions.") <@>
        pretty.indent(details.ppr, 2)

    case class BadInduction(node: Node, details: Kind) extends NodeSummary(node, false):
      def ppr =
        pretty.text("  K-inductive step failed, but didn't find a counterexample.") <@>
        pretty.indent(details.ppr, 2)

    case class Counterexample(node: Node, details: Bmc) extends NodeSummary(node, false):
      def ppr =
        pretty.text("Property false, found a counterexample.") <@>
        pretty.indent(details.ppr, 2)

    def pprJudgments(summary: NodeSummary, judgments: List[system.SystemJudgment]): pretty.Doc =
      val ok  = pretty.Colour.Green.ppr  <> pretty.string("✅")
      val bad = pretty.Colour.Red.ppr    <> pretty.string("❌")
      val huh = pretty.Colour.Yellow.ppr <> pretty.string("❔")
      val success = pretty.string("")
      val unknown = pretty.string("unknown")
      val failed  = pretty.string("failed")
      pretty.vsep(judgments.map { j =>
        val (status,details) = summary match
          case _: OK => (ok, success)
          case Counterexample(_, Bmc.CounterexampleAt(_, trace)) =>
            if trace.propertyKnownFalse(j.consequent)
            then (bad,
              failed <>
              pretty.line <> pretty.indent(j.consequent.ppr <> pretty.colon <+> j.judgment.term.ppr))
            else (huh, unknown)
          case _ =>
            (huh, unknown)
        pretty.indent(status <+> j.judgment.pprObligationShort <+> details <> pretty.Colour.Reset.ppr)
      })

  def declareSystem(n: Node, solver: Solver, options: Translate.Options = Translate.Options()): system.Top =
    val sys = Translate.nodes(n.allNodes, options)
    sys.fundefs.foreach(solver.command)
    sys

  def stepPrefix(pfx: String, i: Int) = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol(pfx), Some(i))))
  def statePrefix(i: Int) = stepPrefix("state", i)
  def rowPrefix(i: Int) = stepPrefix("row", i)

  def callSystemFun(fun: Terms.QualifiedIdentifier, argVars: List[Terms.SortedVar], solver: Solver): Unit =
    val argsV = argVars
    val argsT = argsV.map { v => Terms.QualifiedIdentifier(Terms.Identifier(v.name)) }
    val call = Terms.FunctionApplication(fun, argsT)
    solver.assert(call)

  /** Translate a judgment into an SMT-lib term at a given step. */
  def judgmentTerm(judgment: system.SystemJudgment, step: Int): Terms.Term =
    // The judgment is of form `SoFar(hypotheses) => consequent`, so we
    // add the precondition that all of the hypotheses are true at all steps
    // up to and including now.
    // HACK: is this legit? are we missing the state for SoFar(hypotheses)? Prove it or fix it.
    val antecedents =
      for i <- 0 to step
          h <- judgment.hypotheses
      yield compound.qid(rowPrefix(i)(h))
    compound.implies(
      compound.and(antecedents : _*),
      compound.qid(rowPrefix(step)(judgment.consequent)))

  def asserts(props: List[system.SystemJudgment], step: Int, solver: Solver): Unit =
    props.foreach { prop =>
      solver.assert( judgmentTerm(prop, step) )
    }

  def disprove(props: List[system.SystemJudgment], step: Int): Terms.Term =
    val propsT = props.map(p => compound.not(judgmentTerm(p, step)))
    compound.or(propsT : _*)

  def checkMany(top: Node, options: Options)(using ExecutionContext): Summary =
    val res = top.allNodes.map { n =>
      val r = checkNode(n, options)
      println(r.pprString)
      r
    }
    Summary(res.toList)

  def withSystemSolver[T](
    top: system.Top,
    options: Options
  )(body: Solver => T)(using ExecutionContext): Future[T] =
    Future {
      val solver = options.solver()
      top.fundefs.foreach(solver.command(_))
      try
        body(solver)
      finally
        solver.free()
    }

  def checkNode(top: Node, options: Options)(using ExecutionContext): NodeSummary =
    val sys = Translate.nodes(top.allNodes, options.translate)
    val topS = sys.top
    println(s"Checking '${names.Prefix(top.path).pprString}' with ${topS.system.guarantees.length} properties to check:")

    val bmcF = withSystemSolver(sys, options) { solver =>
      bmc(sys, topS, options.maximumInductiveSteps, solver)
    }
    val indF = withSystemSolver(sys, options) { solver =>
      kind(sys, topS, options.maximumInductiveSteps, solver)
    }
    val feaF = withSystemSolver(sys, options) { solver =>
      feasible(sys, topS, options.requireFeasibilitySteps, solver)
    }

    val judgments = topS.system.guarantees
    val bmcR = Await.result(bmcF, Duration.Inf)
    val summary = bmcR match
      case Bmc.SafeUpTo(_) =>
        val indR = Await.result(indF, Duration.Inf)
        indR match
          case Kind.InvariantMaintainedAt(k) =>
            val feaR = Await.result(feaF, Duration.Inf)
            feaR match
              case CheckFeasible.FeasibleUpTo(_) =>
                NodeSummary.OK(top, k)
              case _ =>
                NodeSummary.Infeasible(top, feaR)
          case _ =>
            NodeSummary.BadInduction(top, indR)

      case _ =>
        NodeSummary.Counterexample(top, bmcR)

    println(pretty.layout(pretty.indent(NodeSummary.pprJudgments(summary, judgments))))
    summary


  def feasible(sys: system.Top, top: system.Node, count: Int, solver: Solver): CheckFeasible =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
      callSystemFun(top.initI, state, solver)
    }

    solver.checkSat().status match
      case CommandsResponses.UnknownStatus => return CheckFeasible.UnknownAt(-1)
      case CommandsResponses.SatStatus     =>
      case CommandsResponses.UnsatStatus   => return CheckFeasible.InfeasibleAt(-1)

    for (step <- 0 until count) {
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      solver.checkSat().status match
        case CommandsResponses.UnknownStatus => return CheckFeasible.UnknownAt(step)
        case CommandsResponses.SatStatus     =>
        case CommandsResponses.UnsatStatus   => return CheckFeasible.InfeasibleAt(step)
    }

    CheckFeasible.FeasibleUpTo(count)


  def bmc(sys: system.Top, top: system.Node, count: Int, solver: Solver): Bmc =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
      callSystemFun(top.initI, state, solver)
    }

    for (step <- 0 until count) {
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      solver.checkSatAssumingX(disprove(top.system.guarantees, step)) { _.status match
        case CommandsResponses.UnknownStatus => return Bmc.UnknownAt(step)
        case CommandsResponses.SatStatus     =>
          val model = solver.command(Commands.GetModel())
          return Bmc.CounterexampleAt(step, Trace.fromModel(step, model))
        case CommandsResponses.UnsatStatus   =>
      }
    }

    Bmc.SafeUpTo(count)


  def kind(sys: system.Top, top: system.Node, count: Int, solver: Solver): Kind =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
    }

    val traces = (0 until count).map { step =>
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      val trace = solver.checkSatAssumingX(disprove(top.system.guarantees, step)) {
        _.status match
          case CommandsResponses.UnknownStatus => return Kind.UnknownAt(step)
          case CommandsResponses.SatStatus     =>
            val model = solver.command(Commands.GetModel())
            Trace.fromModel(step, model)
          case CommandsResponses.UnsatStatus   => return Kind.InvariantMaintainedAt(step)
        }

      asserts(top.system.guarantees, step, solver)
      trace
    }

    Kind.NoGood(count, traces.toList)
