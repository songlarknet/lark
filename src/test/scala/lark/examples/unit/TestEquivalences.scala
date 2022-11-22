package lark.examples.unit

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.node.Invocation
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, Int32}
import lark.meta.driver.{Prove, Dump}

class TestEquivalences extends munit.FunSuite:
  test("sofar-split") {
    Prove.success() {
      new Node(_):
        val in0   = forall[Bool]
        val in1   = forall[Bool]
        val out0  = output[Bool]
        val out1  = output[Bool]
        val out01 = output[Bool]

        import TestEquivalences.SoFar

        out0  := subnode(SoFar(in0)).out
        out1  := subnode(SoFar(in1)).out
        out01 := subnode(SoFar(in0 && in1)).out

        // We want to check whether we found the invariant
        // > out01 == out0 && out1
        // but we need to be careful and add some indirection, otherwise we might
        // just prove it by adding the check itself
        val ok = forall[Bool]
        sorry("out01 implies ok") {
          out01 implies ok
        }
        check("out0 and out1 implies ok") {
          (out0 && out1) implies ok
        }
    }
  }

  test("sofar-split-arr") {
    Prove.success() {
      new Node(_):
        val in0   = forall[Bool]
        val in1   = forall[Bool]
        val out0  = output[Bool]
        val out1  = output[Bool]
        val out01 = output[Bool]

        import TestEquivalences.SoFar2

        out0  := subnode(SoFar2(in0)).out
        out1  := subnode(SoFar2(in1)).out
        out01 := subnode(SoFar2(in0 && in1)).out

        val ok = forall[Bool]
        sorry("out01 implies ok") {
          out01 implies ok
        }
        check("out0 and out1 implies ok") {
          (out0 && out1) implies ok
        }
    }
  }
object TestEquivalences:
  case class SoFar(e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val out  = output[Bool]
    out     := e && fby(True, out)

  case class SoFar2(e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val out  = output[Bool]
    out     := e && (True -> pre(out))
