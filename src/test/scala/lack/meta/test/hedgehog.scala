package lack.meta.test

import lack.meta.base.{num, pretty}
import lack.meta.macros
import _root_.{munit => m}
import _root_.{hedgehog => h}
import scala.reflect.ClassTag

/** Helpers and re-exports of Hedgehog */
object hedgehog:
  export h.Range
  export h.Size
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
    def rational32(nRange: Range[Int], dRange: Range[Int]): Gen[num.Real] =
      for
        n <- Gen.int(nRange)
        d <- Gen.int(dRange)
      yield
        if d == 0 then 0 else num.Real(n) / num.Real(d)


    /** Try to generate a list of unique values from the generator, but no
     * promises.
     *
     * First generates each value with the `main` generator, and if that
     * duplicates a value already generated, then re-generates with the
     * `fallback` generator.
     */
    def tryUniques[S, T](seeds: List[S])
      (main: S => Gen[T])
      (fallback: S => Gen[T])
        : Gen[List[T]] =
      def go(seeds: List[S], ts: List[T]): Gen[List[T]] = seeds match
        case Nil => Gen.constant(ts.reverse)
        case s :: ss =>
          for
            t  <- main(s)
            tX <-
              if ts.contains(t)
              then fallback(s) else Gen.constant(t)
            rest <- go(ss, tX :: ts)
          yield rest

      go(seeds, Nil)

    /** Generate a sublist by discarding some elements. Order is preserved. */
    def sublist[T](ts: List[T]): Gen[List[T]] =
      def go(ts: List[T], acc: List[T]): Gen[List[T]] = ts match
        case Nil => Gen.constant(acc.reverse)
        case t :: ts =>
          for
            keep <- Gen.boolean
            accX =
              if keep
              then t :: acc
              else acc
            r <- go(ts, accX)
          yield r

      go(ts, Nil)

  extension[T] (gen: Gen[T])
    /** Augment generator with an outlier that should only occur rarely */
    def rarely(outlier: Gen[T]): Gen[T] =
      Gen.choice1(gen, gen, gen, outlier)

    def ppr(name: String): h.core.PropertyT[T] =
      gen.forAllWithLog { v => v match
        case v: pretty.Pretty =>
          h.core.ForAll(name, v.pprString)
        case _ =>
          h.core.ForAll(name, v.toString())
      }

  type Property = h.core.PropertyT[Result]
  object Property:
    // XXX: can't re-export all; compiler complains that PropertyTReporting.takeSmallestG contains TailRec annotation with no recursive calls
    export h.Property.{point, fromGen, hoist, writeLog, cover, info, discard, failure, failureA, error, check, checkRandom}

    /** Try to compute a value, discarding any exceptions */
    def try_[T](f: => T): h.core.PropertyT[T] =
      for
        i <- Property.point(try {
          Some(f)
        } catch {
          case e: Exception =>
            None
        })
        _ <-
          if i.isEmpty
          then h.Property.discard
          else Property.point(())
      yield
        i.get

  extension[T] (prop: h.core.PropertyT[T])
    def ppr(name: String): h.core.PropertyT[T] =
      for
        v <- prop
        _ <- Property.writeLog(v match
          case v: pretty.Pretty =>
            h.core.Info(name + ": " + v.pprString)
          case _ =>
            h.core.Info(name + ": " + v.toString()))
      yield
        v
