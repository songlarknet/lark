package lack.meta.test

import lack.meta.base.num
import _root_.{munit => m}
import _root_.{hedgehog => h}

/** Helpers and re-exports of Hedgehog */
object hedgehog:
  export h.Range
  export h.Size
  export h.Property
  export h.PropertyR
  export h.Result
  export h.MonadGen
  export h.propertyT
  export h.Syntax

  type Gen[T] = h.Gen[T]
  object Gen:
    export h.Gen._

    def elementIndexed_[T](xs: Seq[T]): Gen[T] =
      elementIndexed(xs.toIndexedSeq)

    def elementIndexed[T](xs: IndexedSeq[T]): Gen[T] =
      require(xs.nonEmpty)
      int(Range.constant(0, xs.length - 1)).map(i => xs(i))

    def integer(range: Range[num.Integer]): Gen[num.Integer] =
      // Gen.integral uses longs internally so for now just clip to long range
      Gen.long(range.map(num.clampedLong))
        .map(num.Integer(_))

    /** Generate a rational that can be exactly represented as a pair of int32s */
    def rational32: Gen[num.Real] =
      for
        n <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue))
        d <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue))
      yield
        if d == 0 then 0 else num.Real(n) / num.Real(d)
