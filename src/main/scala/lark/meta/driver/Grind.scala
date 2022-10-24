package lark.meta.driver

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty

import lark.meta.core
import lark.meta.core.node.Schedule
import lark.meta.core.node.Eval
import lark.meta.core.term.Val

import lark.meta.smt

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.node.{Base, Invocation}

import lark.meta.target

import scala.collection.immutable
import scala.reflect.ClassTag

/** Grind a program by generating input traces and checking that all of the
 * evaluation traces agree.
 */
object Grind:

  /** Execute all nodes on arbitrary input traces and check that the SMT
   * solver, evaluator, and compiled code all agree. */
  def grind[T <: Base: ClassTag]
    (options: Options = Options())
    (body: Invocation => T)
    (using location: lark.meta.macros.Location)
  : Unit =
    val opts      = Compile.Options(
      basename = "grind",
      output   = None,
      dump     = options.dump,
      withCOptions = c => c.copy(selfInclude = false))
    val compiled  = Compile.getCompiled(opts, body)

    val prepared  = compiled.prepared
    val inputs = prepared.input.zip(prepared.simped)

    inputs.foreach { (original, simp) =>
      val cCode = compiled.headerC <@> compiled.sourceC
      grindNode(original, simp, options, prepared.checks, compiled.schedules, compiled.optsC, cCode)
    }

  /** Grind a node by generating input traces and testing them.
   * We take the raw, original node and the simplified node. We generate values
   * based on the original node and evaluate the simplified to check that they
   * line up.
   */
  def grindNode(original: core.node.Node, simp: core.node.Node, options: Options, checked: names.immutable.RefMap[core.node.Check.Info], schedules: names.immutable.RefMap[Schedule], cOptions: target.C.Options, cCode: pretty.Doc): Unit =
    val info = checked(original.klass)

    val evalopt = Eval.Options(
      core.term.Eval.Options(checkRefinement = options.translate.checkRefinement),
      schedules
    )

    val optCheckC =
      if options.checkC
      then
        val args = original.vars.filter { case (k,v) => v.mode == core.node.Variable.Output }
        if args.isEmpty
        then
          System.err.println(s"Grind: checkC: skipping node ${original.klass.pprString} as node has no outputs.")
          false
        else true
      else false


    println(s"Grinding node ${original.klass.pprString}")
    val solver = smt.Solver.gimme()
    smt.Eval
      .generate(original, solver, options.translate)
      .take(options.count)
      .zipWithIndex
      .foreach { (trace, index) =>
        val dumpKey = Some(original.klass.pprString + "_" + index)
        options.dump.traceP(trace, Dump.Grind.Trace, dumpKey)

        if (options.checkEval)
          options.dump.withTrace(Dump.Grind.Eval, dumpKey) { sink =>
            checkEval(simp, info, trace, evalopt, sink)
          }
        if (optCheckC)
          options.dump.withTrace(Dump.Grind.C, dumpKey) { sink =>
            checkC(simp, info, trace, cOptions, cCode, sink)
          }
    }

  def checkEval(
    nn: core.node.Node,
    info: core.node.Check.Info,
    trace: smt.Trace,
    options: Eval.Options,
    sink: lark.meta.base.debug.Sink
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

      sink.write(
        pretty.text(s"Step ${step}:") <@>
          pretty.indent(
            pretty.text("SMT:") <@>
            pretty.indent(traceP) <@>
            pretty.text("Eval:") <@>
            pretty.indent(names.Namespace.fromMap(heapX).ppr)) <> pretty.line)

      for (k,v) <- outs do
        val vv = heapX(k)
        assert(Val.approx(v, vv),
          s"""Evaluator mismatch in node ${nn.klass.pprString}:
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
    cCode: pretty.Doc,
    sink: lark.meta.base.debug.Sink
  ): Unit =
    import target.C
    import target.c.{Printer => Pr}

    val klass = cOptions.program.classesMap(nn.klass)
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

    val file = cCode <@> main

    sink.write(file)

    target.c.Cbmc.check(file, target.c.Cbmc.defaults)

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
    checkC:    Boolean               = true,
    dump:      Dump                  = Dump.quiet
  ):
    def dump(dump: Dump): Options =
      this.copy(dump = dump)