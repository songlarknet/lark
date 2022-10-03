package lack.meta.driver

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8}
import lack.meta.source.Node
import lack.meta.source.Node.{Builder}
import lack.meta.smt

/** Check that a program satisfies its properties. */
object Check:
  /** Check a node and its subnodes.
   * Will exit with System.exit on failure. */
  def success(options: Options = Options())(f: Node.Invocation => Node): smt.Check.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (!res.ok)
      throw new Exception(s"failed: ${res.pprString}")
    res

  /** Check a node and its subnodes, expecting failure to prove some properties.
   * Will exit with System.exit on unexpected success. */
  def failure(options: Options = Options())(f: Node.Invocation => Node): smt.Check.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (res.ok)
      throw new Exception(s"succeeded but expected failure: ${res.pprString}")
    res

  /** Check a node and its subnodes, expecting some sort of type error.
   * Will exit with System.exit on unexpected success. */
  def error(options: Options = Options())(f: Node.Invocation => Node): Unit =
    try {
      val res = checkResult(options)(f)
      throw new Exception(s"succeeded but expected an error: ${res.pprString}")
    } catch {
      case e: Exception =>
        // ok
    }


  /** Check a node and its subnodes, returning the summary. */
  def checkResult(options: Options = Options())(f: Node.Invocation => Node): smt.Check.Summary =
    given builder: Builder = new Builder(lack.meta.core.node.Builder.Node.top())
    builder.invoke(f)
    val subnodes = builder.nodeRef.subnodes.values
    val subnode = subnodes.toList match
      case List(s) => s
      case List() => assert(false, "No node to check")
      case ls => assert(false, "Too many nodes to check")
    def solver() = smt.Solver.gimme(verbose = options.verbose)
    smt.Check.checkMany(subnode, options.steps, solver, options.translate)

  case class Options(
    verbose: Boolean = false,
    steps: Int = 5,
    translate: smt.Translate.Options = smt.Translate.Options()
  )

  object Options:
    val noRefinement = Options(translate = smt.Translate.Options(checkRefinement = false))
