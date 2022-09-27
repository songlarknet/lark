package lack.examples

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.{Stream => S}
import lack.meta.driver.Check

class TestIntegerCasts extends munit.FunSuite:
  test("widening casts ok") {
    Check.success() {
      new Node(_):
        val xu8 = local[S.UInt8]
        val xu16 = xu8.as[S.UInt16] + u16(0)
        val xi16 = xu8.as[S.Int16] + i16(0)
        val xu32 = xi16.as[S.UInt32] + u32(0)
    }
  }

  test("narrowing casts nok") {
    Check.failure() {
      new Node(_):
        val xu32 = local[S.UInt32]
        val xu8  = xu32.as[S.UInt8] + u8(0)
    }
  }

  test("narrowing casts with requires ok") {
    Check.success() {
      new Node(_):
        val xu32 = local[S.UInt32]
        val xu8  = xu32.as[S.UInt8] + u8(0)
        requires("u32 in bounds") {
          u32(0) <= xu32 && xu32 <= u32(255)
        }
    }
  }

  test("non-causal nok") {
    Check.failure() {
      new Node(_):
        val xu32 = local[S.UInt32]
        xu32 := xu32 + u32(1)
    }
  }

  test("causal nok") {
    Check.failure() {
      new Node(_):
        val xu32 = local[S.UInt32]
        xu32 := fby(u32(0), xu32) + u32(1)
    }
  }
