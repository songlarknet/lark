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
      checkEval(sn, count, options, scheds)
    }

  def schedule(nodes: Iterable[core.node.Builder.Node]): names.immutable.RefMap[Schedule] =
    val scheds = nodes.map { n =>
      val nn = n.freeze
      val graph = Schedule.Slurp(nn).graph()
      val sched = Schedule.scheduleWithNode(nn, graph)
      n.name -> sched
    }
    immutable.SortedMap.from(scheds)

  def checkEval(node: core.node.Builder.Node, count: Int, options: Options, schedules: names.immutable.RefMap[Schedule]): Unit =
    val nn = node.freeze
    val info = core.node.Check.info(nn)

    val evalopt = Eval.Options(
      core.term.Eval.Options(checkRefinement = options.translate.checkRefinement),
      schedules
    )

    println(s"Grinding node ${nn.name.pprString}")
    val solver = smt.Solver.gimme()
    // TODO smt should work on frozen node repr
    smt.Eval.generate(node, solver, options.translate).take(count).foreach { t =>
      val steps = t.steps.map(splitRow(_, nn, info))
      val sys = Eval.node(names.Prefix(List()), nn, evalopt)
      var step = 0
      steps.foldLeft(sys.init) { case (state, (args, outs)) =>
        step = step + 1
        val heapX  = sys.eval(state, args)
        val stateX = sys.update(state, heapX)
        val traceP = pretty.vsep(steps.map { case (a,o) =>
          names.Namespace.fromMap(a).ppr <+>
          pretty.text(":->") <+>
          names.Namespace.fromMap(o).ppr
        })

        for (k,v) <- outs do
          val vv = heapX(k)
          assert(v == vv,
            s"""Evaluator mismatch in node ${nn.name.pprString}:
               |Output ${k.pprString} has value ${v.pprString} in evaluator and ${vv.pprString} in SMT.
               |Expected trace from SMT:
               |${pretty.layout(pretty.indent(traceP))}
               |""".stripMargin)

        stateX
      }
    }

  def castVal(v: core.term.Val, s: core.Sort): core.term.Val = s match
    case r: core.Sort.Refinement => core.term.Val.Refined(r, v)
    case _ => v

  def takeRow(row: smt.Trace.Row, take: names.immutable.ComponentMap[core.node.Variable]): Eval.Heap =
    val rs = row.values
      .filter { case (k,v) => k.prefix.isEmpty && take.contains(k.name) }
      .map { case (k,v) =>
        val s = take(k.name).sort
        val vv = castVal(v, s)
        (k, vv)
      }
    immutable.SortedMap.from(rs)

  def splitRow(row: smt.Trace.Row, node: core.node.Node, info: core.node.Check.Info): (Eval.Heap, Eval.Heap) =
    val args = node.vars.filter { case (k,v) => info.isUnconstrained(k)  }
    val outs = node.vars.filter { case (k,v) => info.isWellDefined(k) }
    val a = takeRow(row, args)
    val o = takeRow(row, outs)
    (a, o)

  case class Options(
    translate: smt.Translate.Options = smt.Translate.Options()
  )

  object Options:
    val noRefinement = Options(translate = smt.Translate.Options(checkRefinement = false))
