package lack.examples.unit

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Node
import lack.meta.source.node.Invocation
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, Int32}
import lack.meta.driver.Check

class TestContractNoGood extends munit.FunSuite:
  test("contract no good") {
    Check.failure() { TestContractNoGood.Lemma(_) }
  }

object TestContractNoGood:
  case class Lemma(invocation: Invocation) extends Node(invocation):
    val undef   = forall[Int32]
    subnode(Contract(undef))

  case class Contract(i: Stream[Int32])(invocation: Invocation) extends Node(invocation):
    requires("input positive") {
      i > 0
    }
    guarantees("input positive (bogus guarantee)") {
      i > 0
    }
