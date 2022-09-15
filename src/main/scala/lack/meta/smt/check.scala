package lack.meta.smt

import lack.meta.base.names
import lack.meta.base.pretty
import lack.meta.core.builder
import lack.meta.core.builder.Node
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}

import lack.meta.smt.solver.Solver
import lack.meta.smt.term.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

object check:
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
      def ppr = pretty.text("Counterexample:") <> pretty.nest(pretty.line <> trace.ppr)
    case class UnknownAt(steps: Int) extends Bmc:
      def ppr = pretty.text(s"Unknown (at step ${steps})")


  sealed trait Kind extends pretty.Pretty
  object Kind:
    case class InvariantMaintainedAt(steps: Int) extends Kind:
      def ppr = pretty.text(s"Invariant maintained with ${steps} steps")
    case class NoGood(steps: Int, traces: List[Trace]) extends Kind:
      def ppr = pretty.text(s"Inductive step failed after trying up to ${steps} steps.") <>
        pretty.nest(traces match
          case _ :: cti1 :: _ =>
            // Print the 1-inductive counterexample-to-induction, as it's the shortest
            // that might hint to the user what's missing
            pretty.line <> pretty.text("1-inductive counterexample:") <@> cti1.ppr
          case _ =>
            pretty.line <> pretty.text("no counterexample-to-induction"))
    case class UnknownAt(steps: Int) extends Kind:
      def ppr = pretty.text(s"Unknown (at step ${steps})")

  case class Trace(steps: List[Trace.Row]) extends pretty.Pretty:
    def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))
  object Trace:
    // HACK TODO not strings
    case class Row(values: List[(String, String)]) extends pretty.Pretty:
      def ppr = pretty.braces(pretty.csep(values.map((k,v) => pretty.text(k) <+> pretty.equal <+> pretty.text(v))))
    // HACK TODO take node and filter out generated bindings
    def fromModel(steps: Int, sexpr: SExpr): Trace =
      def allDefs(s: SExpr): Iterable[(Terms.SSymbol, SExpr)] = s match
        case CommandsResponses.GetModelResponseSuccess(m) =>
          m.flatMap(allDefs)
        case Commands.DefineFun(fd) =>
          if (fd.params.isEmpty) {
            Seq((fd.name, fd.body))
          } else {
            Seq()
          }
        case _ =>
          throw new solver.SolverException(s, "can't parse model counterexample")

      val ds = allDefs(sexpr)

      val stepD = for (i <- 0 to steps) yield {
        val stepI = s"row?${i}."
        val dsI = ds.filter((k,v) => k.name.startsWith(stepI))
        val dsK = dsI.map((k,v) => (k.name.drop(stepI.length), v.toString))
        val dsF = dsK.filter((k,v) => !k.contains("?"))
        val dsS = dsF.toArray.sortBy(_._1).toList
        Row(dsS)
      }

      Trace(stepD.toList)

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

  def declareSystem(n: Node, solver: Solver): system.Top =
    val sys = translate.nodes(n.allNodes)
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
    val propsT = props.map(p => compound.funapp("not", judgmentTerm(p, step)))
    compound.or(propsT : _*)

  def checkMany(top: Node, count: Int, solver: () => Solver): Summary =
    println("Checking top-level node:")
    println(top.pprString)
    println("System translation:")
    println(translate.nodes(top.allNodes).pprString)

    val res = top.allNodes.map { n =>
      val s = solver()
      val r = checkNode(n, count, s)
      println(r.pprString)
      r
    }
    Summary(res.toList)

  def checkNode(top: Node, count: Int, solver: Solver, skipTrivial: Boolean = true): NodeSummary =
    val sys  = declareSystem(top, solver)
    val topS = sys.top
    if (skipTrivial && topS.system.obligations.isEmpty)
      NodeSummary.Skip(top)
    else
      // LODO fix up pretty-printing
      println(s"Node ${names.Prefix(top.path).pprString}:")
      topS.system.assumptions.foreach { o =>
        println(s"  Assume ${o.judgment.pprString}")
      }
      topS.system.obligations.foreach { o =>
        println(s"  Show ${o.judgment.pprString}")
      }

      // TODO: runner / strategy:
      // * run different methods in parallel
      // * when find counterexample, check if remaining props are true
      val bmcR = solver.pushed { bmc(sys, topS, count, solver) }
      bmcR match
        case Bmc.SafeUpTo(_) =>
          val indR = solver.pushed { kind(sys, topS, count, solver) }
          indR match
            case Kind.InvariantMaintainedAt(k) =>
              val feaR = solver.pushed { feasible(sys, topS, count, solver) }
              feaR match
                case CheckFeasible.FeasibleUpTo(_) =>
                  NodeSummary.OK(top, k)
                case _ =>
                  NodeSummary.Infeasible(top, feaR)
            case _ =>
              NodeSummary.BadInduction(top, indR)

        case _ =>
          NodeSummary.Counterexample(top, bmcR)


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

      asserts(top.system.assumptions, step, solver)

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

      asserts(top.system.assumptions, step, solver)

      solver.checkSatAssumingX(disprove(top.system.obligations, step)) { _.status match
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

    var traces: List[Trace] = List()

    for (step <- 0 until count) {
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.assumptions, step, solver)

      solver.checkSatAssumingX(disprove(top.system.obligations, step)) { _.status match
        case CommandsResponses.UnknownStatus => return Kind.UnknownAt(step)
        case CommandsResponses.SatStatus     =>
          val model = solver.command(Commands.GetModel())
          traces +:= Trace.fromModel(step, model)
        case CommandsResponses.UnsatStatus   => return Kind.InvariantMaintainedAt(step)
      }

      asserts(top.system.obligations, step, solver)
    }

    Kind.NoGood(count, traces)
