package lark.examples.unit

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.{Stream => S}
import lark.meta.driver.Prove

class TestIntegerCasts extends munit.FunSuite:
  test("widening casts ok") {
    Prove.success() {
      new Node(_):
        val xu8  = forall[S.UInt8]
        val xu16 = output[S.UInt16]
        val xi16 = output[S.Int16]
        val xu32 = output[S.UInt32]
        xu16    := xu8.as[S.UInt16]  + u16(0)
        xi16    := xu8.as[S.Int16]   + i16(0)
        xu32    := xi16.as[S.UInt32] + u32(0)
    }
  }

  test("narrowing casts nok") {
    Prove.failure() {
      new Node(_):
        val xu32 = forall[S.UInt32]
        val xu8  = output[S.UInt8]
        xu8     := xu32.as[S.UInt8] + u8(0)
    }
  }

  test("narrowing casts with requires ok") {
    Prove.success() {
      new Node(_):
        val xu32 = forall[S.UInt32]
        val xu8  = xu32.as[S.UInt8] + u8(0)
        requires("u32 in bounds") {
          u32(0) <= xu32 && xu32 <= u32(255)
        }
    }
  }

  test("non-causal nok") {
    Prove.failure() {
      new Node(_):
        val xu32 = output[S.UInt32]
        xu32 := xu32 + u32(1)
    }
  }

  test("causal nok") {
    Prove.failure() {
      new Node(_):
        val xu32 = output[S.UInt32]
        xu32 := fby(u32(0), xu32) + u32(1)
    }
  }

  test("bad literal") {
    Prove.error() {
      new Node(_):
        val xu8 = output[S.UInt8]
        xu8 := u8(-5)
    }
  }

  test("bad const propagation") {
    Prove.error() {
      new Node(_):
        val xu8 = output[S.UInt8]
        xu8 := u8(100) + u8(200)
    }
  }