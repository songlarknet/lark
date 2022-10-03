package lack.examples.unit

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, Int32}
import lack.meta.driver.Check

class TestCounterexample extends munit.FunSuite:
  test("counterexample") {
    Check.failure() { new LemmaCounterexample(_) }
  }

  class LemmaCounterexample(invocation: Node.Invocation) extends Node(invocation):
    val counter = local[Int32]
    val undef   = local[Int32]

    counter := fby(i32(0), counter) + undef

    sorry("0 <= undef <= 1") {
      i32(0) <= undef && undef <= i32(1)
    }

    check("falsifiable: counter < 3") {
      counter < 3
    }
