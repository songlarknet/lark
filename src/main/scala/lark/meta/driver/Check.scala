package lark.meta.driver

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.node.{Base, Invocation}
import lark.meta.smt
import lark.meta.core
import scala.reflect.ClassTag

import scala.concurrent.ExecutionContext.Implicits.global

/** Check that a program satisfies its properties. */
object Check:
  /** Check a node and its subnodes.
   * Will exit with System.exit on failure. */
  def success[T <: Base: ClassTag]
    (options: Options = Options())
    (f: Invocation => T)
    (using location: lark.meta.macros.Location)
  : smt.Check.Summary =
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
  : smt.Check.Summary =
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
  : smt.Check.Summary =
    val subnodes = Invoke.allNodes(body)
    val simped   = core.node.transform.InlineBindings.program(subnodes)

    // TODO: check the nodes with an extra "sneaky mode" in the typechecker,
    // which should allow referring to local variables inside merges etc
    // val checked  = core.node.Check.program(sliced, core.node.Check.Options().sneaky)
    smt.Check.checkNodes(simped, options.check)

  case class Options(
    check: smt.Check.Options = smt.Check.Options()
  ):
    def disableRefinement: Options =
      this.copy(check = check.copy(
        translate = check.translate.copy(
          checkRefinement = false)))

    def withMaximumInductiveSteps(k: Int): Options =
      this.copy(check = check.copy(maximumInductiveSteps = k))
