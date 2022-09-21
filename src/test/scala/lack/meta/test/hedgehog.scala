package lack.meta.test

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

    def elementIndexed[T](xs: IndexedSeq[T]): Gen[T] =
      require(xs.nonEmpty)
      int(Range.constant(0, xs.length - 1)).map(i => xs(i))