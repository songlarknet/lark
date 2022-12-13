package lark.examples.unit

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.node.Invocation
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, Int32}
import lark.meta.driver.{Prove, Dump}

/** Simple test cases for SoFar modal operator */
class TestSoFarSoGood extends munit.FunSuite:
  test("sofar-sogood") {
    Prove.success(Prove.Options(dump = Dump.quiet)) {
      new Node(_):
        val in   = forall[Bool]
        val out  = forall[Bool]

        import TestSoFarSoGood.sofar

        val sofar_in  = sofar(in)
        val sofar_out = sofar(out)
        check("box(box(I) => O) => box(box(I) => box(O))") {
          sofar(sofar_in implies out) implies (sofar_in implies sofar_out)
        }
        check("box(box(I) => box(O)) => (box(I) => O)") {
          sofar(sofar_in implies sofar_out) implies (sofar_in implies out)
        }
    }
  }

  test("sofar-sobad") {
    Prove.failure() {
      new Node(_):
        val in   = forall[Bool]
        val out  = forall[Bool]

        import TestSoFarSoGood.sofar

        // Does not hold:
        // step 1: I=T, O=F, (box(I) => O)=F, whole expression true
        // step 2: I=T, O=T, (box(I) => O)=T, but box(O)=F
        check("(box(I) => O) => (box(I) => box(O))") {
          (sofar(in) implies out) implies (sofar(in) implies sofar(out))
        }
    }
  }

object TestSoFarSoGood:
  case class SoFar(e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val out  = output[Bool]
    out     := e && fby(True, out)

  def sofar(e: Stream[Bool])(using builder: Node.Builder): Stream[Bool] =
    lark.meta.source.node.Sugar.subnode(builder)(SoFar(e)).out
