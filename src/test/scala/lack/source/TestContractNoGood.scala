package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.driver.check

object TestContractNoGood:

  def main(args: Array[String]): Unit =
    check.failure() { new Lemma(_) }

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
