package lack.meta.driver

import lack.meta.base.names
import lack.meta.base.names.given
import lack.meta.base.pretty

import lack.meta.core
import lack.meta.core.node.Schedule
import lack.meta.core.node.Eval

import lack.meta.smt

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8}
import lack.meta.source.Node
import lack.meta.source.Node.{Builder}

import scala.collection.immutable

/** Grind a program to find internal errors. */
object Grind:

  /** Use the SMT solver to generate traces, which we compute with evaluator */
  def eval(count: Int, options: Options = Options())(f: Node.Invocation => Node): Unit =
    given builder: Builder = new Builder(lack.meta.core.node.Builder.Node.top())
    builder.invoke(f)
    val subnodes = builder.nodeRef.subnodes.values
    val allnodes = subnodes.flatMap(_.allNodes)
    val scheds   = schedule(allnodes)
    allnodes.foreach { sn =>
      // Skip nodes without arguments - we cannot evaluate them right now
      if sn.vars.exists(_._2.mode == core.node.Variable.Argument) then
        checkEval(sn, count, options, scheds)
    }

  def schedule(nodes: Iterable[core.node.Builder.Node]): names.immutable.RefMap[Schedule] =
    val scheds = nodes.map { n =>
      val nn = n.freeze
      val graph = Schedule.Slurp(nn).graph()
      val sched = graph.scheduleWithNode(nn)
      n.name -> sched
    }
    immutable.SortedMap.from(scheds)

  def checkEval(node: core.node.Builder.Node, count: Int, options: Options, schedules: names.immutable.RefMap[Schedule]): Unit =
    val nn = node.freeze

    val evalopt = Eval.Options(
      core.term.Eval.Options(checkRefinement = options.translate.checkRefinement),
      schedules
    )

    println(s"Node: ${nn.name.pprString}")
    val solver = smt.Solver.gimme()
    // TODO smt should work on frozen node repr
    smt.Eval.generate(node, solver, options.translate).take(count).foreach { t =>
      val steps = t.steps.map(splitRow(_, nn))
      val sys = Eval.node(names.Prefix(List()), nn, evalopt)
      var step = 0
      steps.foldLeft(sys.init) { case (state, (args, outs)) =>
        step = step + 1
        val heapX  = sys.eval(state, args)
        val stateX = sys.update(state, heapX)
        val traceP =
          pretty.vsep(steps.take(step + 1).map { case (a,o) => pretty.value(a) <+> pretty.text(":->") <+> pretty.value(o) })

        for (k,v) <- outs do
          val vv = heapX(k)
          assert(v == vv,
            s"""Evaluator mismatch in node ${nn.name.pprString}:
               |Output ${k.pprString} has value ${v.pprString} in evaluator and ${vv.pprString} in SMT.
               |Trace:
               |${pretty.layout(pretty.indent(traceP))}
               |""".stripMargin)

        stateX
      }
    }

  def takeRow(row: smt.Trace.Row, take: names.immutable.ComponentMap[core.node.Variable]): Eval.Heap =
    val rs = row.values
      .filter { case (k,v) => k.prefix.isEmpty && take.contains(k.name) }
      .map { case (k,v) =>
        val s = take(k.name).sort
        // TODO move to Val or compound
        val vv = s match
          case r: core.Sort.Refinement => core.term.Val.Refined(r, v)
          case _ => v
        (k, vv)
      }
    immutable.SortedMap.from(rs)

  def splitRow(row: smt.Trace.Row, node: core.node.Node): (Eval.Heap, Eval.Heap) =
    val args = node.vars.filter { case (k,v) => v.mode == core.node.Variable.Argument }
    val outs = node.vars.filter { case (k,v) => v.mode == core.node.Variable.Output }
    val a = takeRow(row, args)
    val o = takeRow(row, outs)
    (a, o)

  case class Options(
    translate: smt.Translate.Options = smt.Translate.Options()
  )

  object Options:
    val noRefinement = Options(translate = smt.Translate.Options(checkRefinement = false))
