package lark.meta.smt

import lark.meta.base.{debug, names, pretty}
import lark.meta.base.names.given
import lark.meta.core.node.Node
import lark.meta.driver.Dump

import lark.meta.smt.Term.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import java.util.concurrent.atomic.AtomicReference
import java.util.concurrent.atomic.AtomicBoolean

object Prove:

  case class Options(
    solver:                  debug.Sink => Solver = Solver.gimme,
    translate:               Translate.Options = Translate.Options(),
    maximumInductiveSteps:   Int = 5,
    requireFeasibilitySteps: Int = 5,
  )
  sealed case class Summary(results: List[NodeSummary]) extends pretty.Pretty:
    val ok = results.forall(_.ok)
    def ppr =
      val nok = results.count(!_.ok)
      if (ok)
        pretty.text(s"OK: ${results.length} nodes ok")
      else
        pretty.text(s"NOK: ${nok}/${results.length} nodes failed")

  sealed case class NodeSummary(node: Node, traces: List[(Trace, names.immutable.RefSet)], properties: Property.Map) extends pretty.Pretty:
    def ok =
      properties.forall(_._2.ok)

    def ppr =
      val ok  = pretty.Colour.Green.ppr  <> pretty.string("✅")
      val bad = pretty.Colour.Red.ppr    <> pretty.string("❌")
      val huh = pretty.Colour.Yellow.ppr <> pretty.string("❔")
      // TODO-HI slice traces
      // TODO-HI traces should be tagged as either true counterexample or CtI.
      // TODO-HI feasibility needs to move out of property map, as nodes with no properties can be infeasible
      val tracesP = traces.map(_._1.pprTruncate())
      val propsP  = properties.map { (ref, prop) =>
        val j = prop.judgment
        val statusP = prop.status match
          case Property.Safe    => ok
          case Property.Unsafe  => bad
          case Property.Unknown => huh
        pretty.indent(statusP <+> j.judgment.pprObligationShort <> pretty.colon <+> prop.ppr <> pretty.Colour.Reset.ppr)
      }

      pretty.vsep(tracesP ++ propsP)

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
    val call = compound.funappNoSimp(fun, argsT)
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

  def assumptions(props: List[system.SystemJudgment], step: Int): Terms.Term =
    val propsT = props.map(p => judgmentTerm(p, step))
    compound.and(propsT : _*)

  def disprove(props: List[system.SystemJudgment], step: Int): Terms.Term =
    val propsT = props.map(p => compound.not(judgmentTerm(p, step)))
    compound.or(propsT : _*)

  def withSystemSolver[T](
    top: system.Top,
    options: Options,
    dump: debug.Options,
    stage: debug.Stage,
    dumpKey: Option[String]
  )(body: Solver => T)(using ExecutionContext): Future[T] =
    Future {
      dump.withTrace(stage, dumpKey) { sink =>
        val solver = options.solver(sink)
        top.fundefs.foreach(solver.command(_))
        try
          body(solver)
        finally
          solver.free()
      }
    }

  def checkNode(node: Node, sys: system.Top, options: Options, dump: debug.Options)(using ExecutionContext): NodeSummary =
    val topS = sys.top
    val dumpKey = Some(node.klass.pprString)
    dump.traceP(sys.top, Dump.Prove.System, dumpKey)

    val props = Property.Map.from(topS.system.guarantees.map { j =>
      j.consequent -> Property(j)
    })

    val bmcC = new Channel(props)()
    val indC = bmcC.splitTraces()
    val feaC = bmcC.splitTraces()

    val bmcF = withSystemSolver(sys, options, dump, Dump.Prove.Bmc, dumpKey) { solver =>
      bmc(sys, topS, options.maximumInductiveSteps, solver, bmcC)
    }
    val indF = withSystemSolver(sys, options, dump, Dump.Prove.Kind, dumpKey) { solver =>
      kind(sys, topS, options.maximumInductiveSteps, solver, indC)
    }
    val feaF = withSystemSolver(sys, options, dump, Dump.Prove.Feas, dumpKey) { solver =>
      feasible(sys, topS, options.requireFeasibilitySteps, solver, feaC)
    }

    val judgments = topS.system.guarantees
    Await.result(bmcF, Duration.Inf)
    val summary = bmcC.traces() match
      case List() =>
        Await.result(indF, Duration.Inf)
        Await.result(feaF, Duration.Inf)
        val summa = NodeSummary(node, List(), bmcC.properties())
        if summa.ok
        then summa
        else summa.copy(traces = indC.traces())
      case traces =>
        bmcC.abort()
        val summa = NodeSummary(node, traces, bmcC.properties())
        assert(!summa.ok)
        summa

    summary



  /** Communication channel between processes.
   * Channels can:
   *  publish status of existing properties (eg BMC safe for 5 steps)
   *  signal early abort to others
   *  submit counterexample traces
   * In the future we probably want to be able to add new properties as well.
  */
  class Channel(val initialProperties: Property.Map)(
      abortRef: AtomicBoolean = new AtomicBoolean(false),
      propertiesRef: AtomicReference[Property.Map] = new AtomicReference(initialProperties),
      tracesRef: java.util.concurrent.ConcurrentLinkedQueue[(Trace, names.immutable.RefSet)] = new java.util.concurrent.ConcurrentLinkedQueue()
  ):
    def checkAbort(): Boolean = abortRef.get()
    def abort(): Unit = abortRef.set(true)

    def properties(): Property.Map =
      propertiesRef.get()

    def update(mpProps: Property.Map): Property.Map =
      propertiesRef.accumulateAndGet(mpProps, Property.Map.join)

    def update(props: List[Property]): Property.Map =
      val mpProps = Property.Map.from(props.map(p => (p.judgment.consequent, p)))
      update(mpProps)

    def counterexample(trace: Trace, props: names.immutable.RefSet): Unit =
      tracesRef.add((trace, props))

    def traces(): List[(Trace, names.immutable.RefSet)] =
      val mut = scala.collection.mutable.ArrayBuffer[(Trace, names.immutable.RefSet)]()
      tracesRef.forEach { t => mut.addOne(t) }
      mut.toList

    /** Construct a new channel with the same underlying properties and abort
     * signal, but with a separate trace queue. This is so we can prioritise
     * real counterexamples from bmc but fall back to inductive traces if there
     * aren't any real ones.
     */
    def splitTraces(): Channel =
      new Channel(initialProperties)(abortRef, propertiesRef,
        new java.util.concurrent.ConcurrentLinkedQueue())

    /** Loop for up to count times, or early exit if abort is triggered (by another thread) */
    def loop(count: Int)(body: Int => Unit): Unit =
      for (step <- 0 until count) {
        if checkAbort() then return
        body(step)
      }

    /** Given some predicate over properties like "P is unknown for BMC at step i",
     * apply body to list of unknown properties until there are no more unknown
     * properties.
     * Each application of body must reduce the size of the set to ensure
     * termination.
    */
    def fix(pred: Property => Boolean)(body: List[Property] => Unit): Unit =
      var unknown = properties().values.filter(pred)
      while (unknown.nonEmpty) {
        if checkAbort() then return
        body(unknown.toList)
        val unknownX = properties().values.filter(pred)
        assert(unknownX.size < unknown.size)
        unknown = unknownX
      }



  def bmc(sys: system.Top, top: system.Node, count: Int, solver: Solver, channel: Channel): Unit =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
      callSystemFun(top.initI, state, solver)
    }

    channel.loop(count) { step =>
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      channel.fix (_.bmc.at(step) == Property.Unknown) { unknowns =>
        solver.checkSatAssumingX(disprove(unknowns.map(_.judgment), step)) { _.status match
          case CommandsResponses.UnknownStatus =>
            // TODO simplify model, slice, abstract?
            channel.update(
              unknowns.map(_.withBmc(Property.Disprove(Property.Unknown, step)))
            )
          case CommandsResponses.SatStatus     =>
            val model = solver.command(Commands.GetModel())
            val trace = Trace.fromModel(step, model)
            val bads  = unknowns.filter(p => trace.propertyKnownFalse(p.judgment.consequent))
            val badsR = scala.collection.immutable.SortedSet.from(bads.map(_.judgment.consequent))
            channel.update(
              bads.map(_.withBmc(Property.Disprove(Property.Unsafe, step)))
            )
            channel.counterexample(trace, badsR)

          case CommandsResponses.UnsatStatus   =>
            channel.update(
              unknowns.map(_.withBmc(Property.Disprove(Property.Safe, step)))
            )
        }
      }
    }

  def kind(sys: system.Top, top: system.Node, count: Int, solver: Solver, channel: Channel): Unit =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
    }

    channel.loop(count) { step =>
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      channel.fix (_.kind.at(step) == Property.Unknown) { unknowns =>
        val unknownsJ = unknowns.map(_.judgment)
        val unknownAssumptions =
          for stepX <- 0 to step - 1
          yield assumptions(unknownsJ, stepX)
        val unknownGoal =
          disprove(unknownsJ, step)

        // Assume all properties that are known invariant
        val invariantsJ =
          channel.properties().values.filter { p =>
            p.status == Property.Safe || (p.status == Property.Unknown && p.kind.at(step) == Property.Safe) }
            .map(_.judgment).toList
        val invariantsSteps =
          for stepX <- 0 to step
          yield assumptions(invariantsJ, stepX)

        val assumingX =
          compound.and(
            compound.and(invariantsSteps*),
            compound.and(unknownAssumptions*),
            unknownGoal)

        solver.checkSatAssumingX(assumingX) { _.status match
          case CommandsResponses.UnknownStatus =>
            // TODO simplify model, slice, abstract?
            channel.update(
              unknowns.map(_.withKind(Property.Prove(Property.Unknown, step)))
            )
          case CommandsResponses.SatStatus     =>
            val model = solver.command(Commands.GetModel())
            val trace = Trace.fromModel(step, model)
            val bads  = unknowns.filter(p => trace.propertyKnownFalse(p.judgment.consequent))
            val badsR = scala.collection.immutable.SortedSet.from(bads.map(_.judgment.consequent))
            channel.update(
              bads.map(_.withKind(Property.Prove(Property.Unsafe, step)))
            )
            // Only log traces at step 1 (normal induction) because these are
            // not too long but might contain enough information to be useful.
            if step == 1 then
              channel.counterexample(trace, badsR)

          case CommandsResponses.UnsatStatus   =>
            channel.update(
              unknowns.map(_.withKind(Property.Prove(Property.Safe, step)))
            )
        }
      }
    }


  def feasible(sys: system.Top, top: system.Node, count: Int, solver: Solver, channel: Channel): Unit =
    {
      val state = top.paramsOfNamespace(statePrefix(0), top.system.state)
      solver.declareConsts(state)
      callSystemFun(top.initI, state, solver)
    }

    def update(status: Property.Status, steps: Int) =
      val feas = Property.Map.from(
        channel.initialProperties.mapValues { v => v.withFeas(Property.Disprove(status, steps)) })
      channel.update(feas)

    solver.checkSat().status match
      case CommandsResponses.UnknownStatus =>
        update(Property.Unknown, -1)
        return
      case CommandsResponses.SatStatus     =>
      case CommandsResponses.UnsatStatus   =>
        update(Property.Unsafe, -1)
        return

    channel.loop(count) { step =>
      val state  = top.paramsOfNamespace(statePrefix(step), top.system.state)
      val stateS = top.paramsOfNamespace(statePrefix(step + 1), top.system.state)
      val row    = top.paramsOfNamespace(rowPrefix(step), top.system.row)

      solver.declareConsts(row ++ stateS)

      callSystemFun(top.stepI, state ++ row ++ stateS, solver)

      asserts(top.system.relies, step, solver)
      asserts(top.system.sorries, step, solver)

      solver.checkSat().status match
        case CommandsResponses.UnknownStatus =>
          update(Property.Unknown, step)
          return
        case CommandsResponses.SatStatus     =>
          update(Property.Safe, step)
        case CommandsResponses.UnsatStatus   =>
          update(Property.Unsafe, step)
          return
    }
