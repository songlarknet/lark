package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.driver.check

class TestCounterexample extends munit.FunSuite:
  test("counterexample") {
    check.failure() { new LemmaCounterexample(_) }
  }

  class LemmaCounterexample(invocation: NodeInvocation) extends Node(invocation):
    val counter = local[Int32]
    val undef   = local[Int32]

    counter := i32(0) -> (pre(counter) + undef)

    sorry("undef <= 1") {
      undef <= 1
    }

    check("falsifiable: counter < 3") {
      counter < 3
    }
