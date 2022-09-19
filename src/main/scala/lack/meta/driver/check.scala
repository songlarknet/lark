package lack.meta.driver

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, UInt8}
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt

object check:
  /** Check a node and its subnodes.
   * Will exit with System.exit on failure. */
  def success(options: Options = Options())(f: NodeInvocation => Node): smt.check.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (!res.ok)
      throw new Exception(s"failed: ${res.pprString}")
    res

  /** Check a node and its subnodes, expecting failure.
   * Will exit with System.exit on unexpected success. */
  def failure(options: Options = Options())(f: NodeInvocation => Node): smt.check.Summary =
    val res = checkResult(options)(f)
    println(res.pprString)
    if (res.ok)
      throw new Exception(s"succeeded but expected failure: ${res.pprString}")
    res

  /** Check a node and its subnodes, returning the summary. */
  def checkResult(options: Options = Options())(f: NodeInvocation => Node): smt.check.Summary =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    builder.invoke(f)
    val subnodes = builder.nodeRef.subnodes.values
    val subnode = subnodes.toList match
      case List(s) => s
      case List() => assert(false, "No node to check")
      case ls => assert(false, "Too many nodes to check")
    def solver() = smt.solver.gimme(verbose = options.verbose)
    smt.check.checkMany(subnode, options.steps, solver)

  case class Options(
    verbose: Boolean = false,
    steps: Int = 5,
  )
