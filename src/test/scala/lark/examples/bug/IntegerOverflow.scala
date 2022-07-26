package lark.examples.bug

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, Int32, UInt8}
import lark.meta.driver.Prove
import lark.meta.smt.Translate

// Specification bug: surprising behaviour, but sound.
// We get overflows in contexts where the value is never used.
class IntegerOverflow extends munit.FunSuite:
  test("pre: disable overflow check ok") {
    val opt = Prove.Options().disableRefinement
    Prove.success(opt) { BugPre(_) }
  }

  test("pre: overflow check fails") {
    Prove.failure() { BugPre(_) }
  }

  case class BugPre(invocation: Node.Invocation) extends Node(invocation):
    val zeros    = local[Int32]
    val increment = local[Int32]

    // The observable value of zeros is always 0. However, at the first step
    // the value of pre(zeros) is undefined and we increment it by one, then
    // discard that value. If pre(zeros) is 2147483647 then the increment will
    // overflow.
    zeros     := i32(0) -> (pre(zeros) + increment)
    increment := i32(1) -> i32(0)

    // This is proved fine.
    check("zeros = 0") {
      zeros == 0
    }

  test("saturating counter: 254 ok") {
    Prove.success() { BugSaturatingCounter(254) }
  }

  test("saturating counter: 255 fails") {
    Prove.failure() { BugSaturatingCounter(255) }
  }

  case class BugSaturatingCounter(limit: Int)(invocation: Node.Invocation) extends Node(invocation):
    val count = local[UInt8]

    val prec = fby(u8(0), count)
    count := ifthenelse(prec < limit, prec + 1, prec)
