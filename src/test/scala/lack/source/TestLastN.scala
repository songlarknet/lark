package lack.source

import lack.meta.base.Integer
import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, UInt8}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt

object TestLastN:

  def main(args: Array[String]): Unit =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    val lem = LemmaLastN(3)
    println(builder.nodeRef.pretty)

    def solver() = smt.solver.gimme(verbose = false)

    println(s"feasible: ${smt.check.feasible(builder.nodeRef, 2, solver())}")
    println(s"bmc:      ${smt.check.bmc(builder.nodeRef, 4, solver())}")
    println(s"k-ind:    ${smt.check.kind(builder.nodeRef, 2, solver())}")


  class LemmaLastN(n: Integer, invocation: NodeInvocation) extends Node(invocation):
    val e      = local[Bool]
    val lastN  = LastN(n,     e)
    val lastSN = LastN(n + 1, e)
    property("invariant LastN(n, e).count <= LastN(n + 1, e).count <= LastN(n, e).count + 1") {
      lastN.count <= lastSN.count && lastSN.count <= lastN.count + 1
    }
    property("forall n e. LastN(n + 1, e) ==> LastN(n, e)") {
      lastSN.out ==> lastN.out
    }

  object LemmaLastN:
    def apply(n: Integer)(using builder: Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        invocation.metaarg("n", n)
        new LemmaLastN(n, invocation)
      }

  class LastN(n: Integer, e: Stream[Bool], invocation: NodeInvocation) extends Node(invocation):
    require(n <= 255)

    val count     = local[UInt8]
    val out       = output[Bool]
    val pre_count = u8(0) -> pre(count)

    count := cond(
      when(e && pre_count <  n) { pre_count + 1 },
      when(e && pre_count >= n) { n },
      otherwise                 { 0 }
    )

    val chk = out   := count >= n

    property("0 <= count <= n") {
      u8(0) <= count && count <= n
    }

    // property("count <= ${n - 1} (not true!)") {
    //   count <= (n - 1)
    // }

  object LastN:
    def apply(n: Integer, e: Stream[stream.Bool])(using builder: Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        invocation.metaarg("n", n)
        new LastN(n, invocation.arg("e", e), invocation)
      }
