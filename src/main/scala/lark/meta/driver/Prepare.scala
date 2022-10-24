package lark.meta.driver

import lark.meta.base.names

import lark.meta.core
import lark.meta.source.Node
import lark.meta.source.node.{Base, Builder, Invocation, Sugar}
import scala.reflect.ClassTag

/** Node preparation common to checking and compiling */
object Prepare:
  /** Freeze the source representation into core */
  def freeze[T <: Base: ClassTag](dump: Dump, body: Invocation => T): List[core.node.Node] =
    val top    = core.node.Builder.Node.top()
    given builder: Builder = new Builder(top)
    val sn      = Sugar.subnode(builder)(body)
    val frozen  = top.subnodes.values.map(_.freeze)
    val flatten = frozen.flatMap(_.allNodes).toList

    dump.traces(flatten, Dump.Prepare.Input)

    flatten

  /** Prepare for compilation */
  def prepareCompile[T <: Base: ClassTag](dump: Dump, body: Invocation => T): Prepared =
    val frozen = freeze(dump, body)

    val sliced = core.node.transform.Slice.program(frozen)
    dump.traces(sliced, Dump.Prepare.Slice)

    val simped   = core.node.transform.InlineBindings.program(sliced)

    dump.traces(simped, Dump.Prepare.Simp)

    // Typecheck after slicing and simplifying because the simplified program is hopefully closer
    // to what the user wrote.
    val checks = core.node.Check.program(simped, core.node.Check.Options())
    dump.traces(checks.values, Dump.Prepare.Typecheck)

    Prepared(frozen, simped.toList, checks)

  case class Prepared(
    input:  List[core.node.Node],
    simped: List[core.node.Node],
    checks: names.immutable.RefMap[core.node.Check.Info])

  /** Prepare for checking */
  def prepareCheck[T <: Base: ClassTag](dump: Dump, body: Invocation => T): List[core.node.Node] =
    val frozen = freeze(dump, body)
    val simped   = core.node.transform.InlineBindings.program(frozen)
    dump.traces(simped, Dump.Prepare.Simp)
    // TODO: check the nodes with an extra "sneaky mode" in the typechecker,
    // which should allow referring to local variables inside merges etc
    simped.toList