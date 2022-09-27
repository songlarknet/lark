package lack.examples

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

    counter := i32(0) -> (pre(counter) + undef)

    sorry("undef <= 1") {
      undef <= 1
    }

    check("falsifiable: counter < 3") {
      counter < 3
    }
