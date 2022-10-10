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

import lack.meta.target

import scala.collection.immutable

/** Grind a program by generating input traces and checking that all of the
 * evaluation traces agree.
 */
object Grind:

  /** Execute all nodes on arbitrary input traces and check that the SMT
   * solver, evaluator, and compiled code all agree. */
  def grind(options: Options = Options())(f: Node.Invocation => Node): Unit =
    given builder: Builder = new Builder(lack.meta.core.node.Builder.Node.top())
    builder.invoke(f)
    val subnodes  = builder.nodeRef.subnodes.values
    val allnodes  = subnodes.flatMap(_.allNodes)
    val frozen    = allnodes.map(_.freeze)
    val checked   = core.node.Check.program(frozen, core.node.Check.Options())
    val schedules = Compile.schedules(frozen)
    val program   = core.obc.FromNode.program(frozen, schedules)
    val cOptions  = target.C.Options(basename = "grind", program)
    val cCode     = target.C.headersource(cOptions)

    allnodes.foreach { sn =>
      grindNode(sn, options, checked, schedules, cOptions, cCode)
    }

  /** Grind a node by generating input traces and testing them. */
  def grindNode(node: core.node.Builder.Node, options: Options, checked: names.immutable.RefMap[core.node.Check.Info], schedules: names.immutable.RefMap[Schedule], cOptions: target.C.Options, cCode: pretty.Doc): Unit =
    val nn = node.freeze
    val info = checked(nn.name)

    val evalopt = Eval.Options(
      core.term.Eval.Options(checkRefinement = options.translate.checkRefinement),
      schedules
    )

    val optCheckC =
      if options.checkC
      then
        val args = node.vars.filter { case (k,v) => v.mode == core.node.Variable.Output }
        if args.isEmpty
        then
          System.err.println(s"Grind: checkC: skipping node ${node.name.pprString} as node has no outputs.")
          false
        else true
      else false


    println(s"Grinding node ${nn.name.pprString}")
    val solver = smt.Solver.gimme()
    // TODO smt should work on frozen node repr
    smt.Eval
      .generate(node, solver, options.translate)
      .take(options.count)
      .foreach { trace =>
        if (options.checkEval)
          checkEval(nn, info, trace, evalopt)
        if (optCheckC)
          checkC(nn, info, trace, cOptions, cCode)
    }

  def checkEval(
    nn: core.node.Node,
    info: core.node.Check.Info,
    trace: smt.Trace,
    options: Eval.Options
  ): Unit =
    val steps = trace.steps.map(splitRowEval(_, nn, info))
    val sys = Eval.node(names.Prefix(List()), nn, options)
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

  def checkC(
    nn: core.node.Node,
    info: core.node.Check.Info,
    trace: smt.Trace,
    cOptions: target.C.Options,
    cCode: pretty.Doc
  ): Unit =
    import target.C
    import target.c.{Printer => Pr}

    val klass = cOptions.program.classesMap(nn.name)
    val reset = klass.methodsMap(core.obc.Obc.Method.reset)
    val step  = klass.methodsMap(core.obc.Obc.Method.step)

    val stateT    = C.Names.stateP(klass.name)
    val stepOutT  = C.Names.outP(klass.name, step.name)

    val state     = pretty.text("state")
    val stepOut   = pretty.text("out")
    val statePtr  = Pr.Term.address(state)
    val stepOutPtr= Pr.Term.address(stepOut)

    val steps  = trace.steps.map(splitRowC(_, nn, info))
    val stepsP = steps.map { case (ins,outs) =>
      val argsV = step.params.map { p => ins(names.Ref.fromComponent(p.name)) }
      val args  = argsV.map(Pr.Term.val_(_))

      val asserts =
        for
          (o,v) <- outs
          got    = stepOut <> pretty.dot <> Pr.Ident.ref(o)
          expect = Pr.Term.val_(v)
        yield
          Pr.Stm.assertEquals(got, expect, v.sort)

      pretty.vsep(
        Pr.Stm.fun(C.Names.method(klass.name, step.name),
          statePtr +: args :+ stepOutPtr) +:
        asserts.toList)
    }

    val main =
      pretty.text("int main()") <+> Pr.Stm.block(
        stateT   <+> state   <> pretty.semi <@>
        stepOutT <+> stepOut <> pretty.semi <@>
        Pr.Stm.fun(C.Names.method(klass.name, reset.name), List(statePtr)) <@>
        pretty.line <>
        pretty.vsep(stepsP)
      )

    target.c.Cbmc.check(cCode <@> main, target.c.Cbmc.defaults)

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

  /** Evaluator can inject values for any undefined value as well as look
   * at any of the intermediate values.
   */
  def splitRowEval(row: smt.Trace.Row, node: core.node.Node, info: core.node.Check.Info): (Eval.Heap, Eval.Heap) =
    val args = node.vars.filter { case (k,v) => info.isUnconstrained(k)  }
    val outs = node.vars.filter { case (k,v) => info.isWellDefined(k) }
    val a = takeRow(row, args)
    val o = takeRow(row, outs)
    (a, o)

  /** C can only inspect the marked outputs */
  def splitRowC(row: smt.Trace.Row, node: core.node.Node, info: core.node.Check.Info): (Eval.Heap, Eval.Heap) =
    val args = node.vars.filter { case (k,v) => info.isUnconstrained(k) }
    val outs = node.vars.filter { case (k,v) => v.mode == core.node.Variable.Output }
    val a = takeRow(row, args)
    val o = takeRow(row, outs)
    (a, o)

  case class Options(
    count:     Int                   = 100,
    translate: smt.Translate.Options = smt.Translate.Options(),
    checkEval: Boolean               = true,
    checkC:    Boolean               = true
  )
