package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt

object TestContractNoGood:

  def main(args: Array[String]): Unit =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    builder.invoke(new Lemma(_))
    def solver() = smt.solver.gimme(verbose = false)
    smt.check.checkMany(builder.nodeRef, 1, solver)

  class Lemma(invocation: NodeInvocation) extends Node(invocation):
    val undef   = local[Int32]

    builder.invoke(i => new Contract(i.arg("i", undef), i))

  class Contract(i: Stream[Int32], invocation: NodeInvocation) extends Node(invocation):
    requires("input positive") {
      i > 0
    }
    guarantees("input positive (bogus guarantee)") {
      i > 0
    }
