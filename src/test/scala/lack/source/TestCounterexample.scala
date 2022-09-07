package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt

object TestCounterexample:

  def main(args: Array[String]): Unit =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    builder.invoke(new LemmaCounterexample(_))
    def solver() = smt.solver.gimme(verbose = false)
    smt.check.checkMany(builder.nodeRef, 4, solver)

  class LemmaCounterexample(invocation: NodeInvocation) extends Node(invocation):
    val counter = local[Int32]

    counter := i32(0) -> (pre(counter) + 1)

    property("falsifiable: counter < 3") {
      counter < 3
    }
