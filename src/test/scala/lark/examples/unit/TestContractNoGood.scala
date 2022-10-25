package lark.examples.unit

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.node.Invocation
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, Int32}
import lark.meta.driver.Prove

class TestContractNoGood extends munit.FunSuite:
  test("contract no good") {
    Prove.failure() { TestContractNoGood.Lemma(_) }
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
