package lack.examples

import lack.meta.base.num.Integer
import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Stream.{SortRepr, Bool, UInt8}
import lack.meta.source.Stream
import lack.meta.source.Node
import lack.meta.driver.{Check, Grind}

class TestLastN extends munit.FunSuite:
  test("lastN") {
    Check.success() { new LemmaLastN(3, _) }
  }

  test("lastN compile") {
    lack.meta.driver.Compile.compile() { new LemmaLastN(3, _) }
  }

  test("Grind.eval") {
    Grind.eval(100) { new LemmaLastN(3, _) }
  }

  class LemmaLastN(n: Integer, invocation: Node.Invocation) extends Node(invocation):
    val e      = forall[Bool]
    val lastN  = LastN(n,     e)
    val lastSN = LastN(n + 1, e)
    check("invariant LastN(n, e).count <= LastN(n + 1, e).count <= LastN(n, e).count + 1") {
      lastN.count <= lastSN.count && lastSN.count <= lastN.count + 1
    }
    check("forall n e. LastN(n + 1, e) ==> LastN(n, e)") {
      lastSN.out ==> lastN.out
    }

  class LastN(n: Integer, e: Stream[Bool], invocation: Node.Invocation) extends Node(invocation):
    require(n <= 255)

    val count     = output[UInt8]
    val out       = output[Bool]
    val pre_count = u8(0) -> pre(count)

    count := cond(
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

  object LastN:
    def apply(n: Integer, e: Stream[Bool])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new LastN(invocation.arg("n", n), invocation.arg("e", e), invocation)
      }
