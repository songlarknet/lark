package lark.meta.driver

import lark.meta.base.pretty

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.node.{Base, Invocation}
import lark.meta.smt
import lark.meta.core
import scala.reflect.ClassTag

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, Future}
import scala.concurrent.duration.Duration

/** Prove that a program satisfies its properties. */
object Prove:
  /** Check a node and its subnodes.
   * Will exit with System.exit on failure. */
  def success[T <: Base: ClassTag]
    (options: Options = Options())
    (f: Invocation => T)
    (using location: lark.meta.macros.Location)
  : smt.Prove.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (!res.ok)
      throw new Exception(s"failed: ${res.pprString}")
    res

  /** Check a node and its subnodes, expecting failure to prove some properties.
   * Will exit with System.exit on unexpected success. */
  def failure[T <: Base: ClassTag]
    (options: Options = Options())
    (f: Invocation => T)
    (using location: lark.meta.macros.Location)
  : smt.Prove.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (res.ok)
      throw new Exception(s"succeeded but expected failure: ${res.pprString}")
    res

  /** Check a node and its subnodes, expecting some sort of type error.
   * Will exit with System.exit on unexpected success. */
  def error[T <: Base: ClassTag]
    (options: Options = Options())
    (f: Invocation => T)
    (using location: lark.meta.macros.Location)
  : Unit =
    try {
      val res = checkResult(options)(f)
      throw new Exception(s"succeeded but expected an error: ${res.pprString}")
    } catch {
      case e: Exception =>
        // ok
    }


  /** Check a node and its subnodes, returning the summary. */
  def checkResult[T <: Base: ClassTag]
    (options: Options = Options())
    (body: Invocation => T)
    (using location: lark.meta.macros.Location)
  : smt.Prove.Summary =
    val prepared = Prepare.prepareCheck(options.dump, body)

    // PERF: this could be concurrent
    val equivalences =
      core.node.analysis.Equivalence.program(prepared, options.dump, Dump.Prove.Equiv)
    val futures = prepared.map { node =>
      val sys   = smt.Translate.nodes(node.allNodes, options.check.translate)
      val equiv = equivalences(node.klass)
      (node, sys, Future {
        smt.Prove.checkNode(node, sys, equiv, options.check, options.dump)
      })
    }
    val results = futures.map { (node, sys, future) =>
      println(s"Checking '${node.klass.pprString}' with ${sys.top.system.guarantees.length} properties to check:")
      val r = Await.result(future, Duration.Inf)
      println(pretty.layout(r.pprWith(options.trace)))
      r
    }
    smt.Prove.Summary(results)

  case class Options(
    check: smt.Prove.Options = smt.Prove.Options(),
    trace: smt.Trace.Options = smt.Trace.Options(),
    dump:  Dump              = Dump.quiet,
  ):
    def disableRefinement: Options =
      this.copy(check = check.copy(
        translate = check.translate.copy(
          checkRefinement = false)))

    def withMaximumInductiveSteps(k: Int): Options =
      this.copy(check = check.copy(maximumInductiveSteps = k))

    def dump(dump: Dump): Options =
      this.copy(dump = dump)

    /** When printing a counterexample, specify what to "focus" on by hiding
     * some bindings. The default behaviour is to print bindings that the
     * failing property transitively refers to, as well as any bindings related
     * to any assumptions or subproperties that might restrict the behaviour
     * or these bindings.
     * If you find you want less information, try `focusFailingProperty`.
     * If you want a more information, try `focusAllProperties` or even
     * `everything`.
     */
    def focus(focus: smt.Trace.Options.Focus): Options =
      this.copy(trace = trace.copy(focus = focus))

    /** When printing a counterexample, "focus" on the properties by only
     * printing the bindings that the properties actually depend upon. This
     * filters out some implementation details but can print stuff that's not
     * directly relevant to the failure.
     */
    def focusMutualInfluence: Options =
      focus(smt.Trace.Options.FocusMutualInfluence)

    /** When printing a counterexample, "focus" on the failing property by only
     * printing the bindings that the failing property actually depends upon.
     */
    def focusFailingProperty: Options =
      focus(smt.Trace.Options.FocusFailingProperty)

    /** When printing a counterexample, "focus" on the properties by only
     * printing the bindings that the properties actually depend upon. This
     * filters out some implementation details but can print stuff that's not
     * directly relevant to the failure.
     */
    def focusAllProperties: Options =
      focus(smt.Trace.Options.FocusAllProperties)

    /** When printing a counterexample, show all of the subnodes without
     * filtering any out. Local bindings inside subnodes can still be hidden
     * by the `hideSubnodeBindings` setting; see `everything` to really trace
     * everything.
     */
    def focusEverything: Options =
      focus(smt.Trace.Options.FocusEverything)

    /** When displaying subnodes in a trace, hide the local bindings at the
     * given depth or deeper.
     */
    def hideSubnodeBindings(hideSubnodeBindingsAtDepth: Int = 1): Options =
      this.copy(trace = trace.copy(
        hideSubnodeBindingsAtDepth = hideSubnodeBindingsAtDepth))

    /** When printing a counterexample, show all of the local variables and
     * subnodes without filtering any out.
     * and show all of the bindings.
     */
    def everything: Options =
      focus(smt.Trace.Options.FocusEverything).hideSubnodeBindings(Int.MaxValue)
