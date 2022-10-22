package lark.examples

import lark.meta.base.num.Integer
import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.Stream
import lark.meta.source.Node
import lark.meta.driver.{Check, Grind}

class TestLastN extends munit.FunSuite:
  test("lastN") {
    Check.success() { LemmaLastN(3) }
  }

  test("lastN compile") {
    lark.meta.driver.Compile.compile() { LemmaLastN(3) }
  }

  test("Grind") {
    Grind.grind() { LemmaLastN(3) }
  }

  case class LemmaLastN(n: Integer)(invocation: Node.Invocation) extends Node(invocation):
    val e      = forall[Bool]
    val lastN  = subnode(LastN(n,     e))
    val lastSN = subnode(LastN(n + 1, e))
    check("invariant LastN(n, e).count <= LastN(n + 1, e).count <= LastN(n, e).count + 1") {
      lastN.count <= lastSN.count && lastSN.count <= lastN.count + 1
    }
    check("forall n e. LastN(n + 1, e) ==> LastN(n, e)") {
      lastSN.out ==> lastN.out
    }

  case class LastN(n: Integer, e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    require(n <= 255)

    val count     = output[UInt8]
    val out       = output[Bool]
    val pre_count = u8(0) -> pre(count)

    count := select(
      when(e && pre_count <  n) { pre_count + 1 },
      when(e && pre_count >= n) { n },
      otherwise                 { 0 }
    )

    val chk = out   := count >= n

    check("0 <= count <= n") {
      u8(0) <= count && count <= n
    }

    // check("count <= ${n - 1} (not true!)") {
    //   count <= (n - 1)
    // }
