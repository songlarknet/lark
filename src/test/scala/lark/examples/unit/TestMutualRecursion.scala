package lark.examples.unit

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.node.Invocation
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, Int32}
import lark.meta.driver.{Prove, Dump}

class TestMutualRecursion extends munit.FunSuite:
  test("rec0-rec1") {
    Prove.success() {
      new Node(_):
        val rec0  = output[Int32]
        val rec1  = output[Int32]

        rec0 := rec1 + fby(i32(0), rec0)
        rec1 := fby(i32(0), rec0) + fby(i32(0), rec1)

        check("zero") { rec0 == 0 }

        // LODO: the 'normalise' transform in equivalence doesn't always take
        // the recursive bindings completely because it doesn't support nested
        // µ-bindings.
        // For this pair the correct bindings would be:
        // > rec0 = µ. (µ. (0 -> pre µ1) + (0 -> pre µ0)) + (0 -> pre µ0)
        // > rec1 = µ. (0 -> pre (µ. µ1 + (0 -> pre µ0))) + (0 -> pre µ0)
        //
        // but we instead get something that looks like:
        // > rec0 = µ. ((0 -> pre µ0) + (0 -> pre rec1)) + (0 -> pre µ0)
        // > rec1 = µ. (0 -> pre rec0) + (0 -> pre µ0)
        //
        // where some of the names remain. This should still be sound -- the
        // equation is still true -- it's just not going to unify with other
        // bindings with the same structure.
    }
  }

  test("alt") {
    Prove.success() {
      new Node(_):
        val tf = output[Bool]
        val ft = output[Bool]

        tf := fby(True, ft)
        ft := fby(False, tf)

        check("at least one") { tf || ft }
        check("never both") { !(tf && ft) }
    }
  }
