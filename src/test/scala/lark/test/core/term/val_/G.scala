package lark.test.core.term.val_

import lark.meta.base.num
import lark.meta.base.names.Ordering_Ref
import lark.meta.core.term.Eval
import lark.meta.core.term.Check
import lark.meta.core.term.Val
import lark.meta.core.Sort

import lark.test.hedgehog._

object G:
  def value(sort: Sort): Gen[Val] = sort match
    case Sort.Bool =>
      Gen.boolean.map(Val.Bool(_))
    case Sort.ArbitraryInteger =>
      Gen.choice1(
        Gen.constant(Val.Int(0)),
        Gen.constant(Val.Int(1)),
        Gen.constant(Val.Int(-1)),
        niceInts(Long.MinValue, Long.MaxValue)
          .map(Val.Int(_)),
      )
    case s: Sort.BoundedInteger =>
      def rf(i: lark.meta.base.num.Integer) = Val.Refined(s, Val.Int(i))
      Gen.choice1(
        Gen.constant(rf(0)),
        Gen.constant(rf(1)),
        niceInts(s.minInclusive, s.maxInclusive)
          .map(rf)
      )

    case Sort.Real =>
      Gen.choice1(
        Gen.constant(Val.Real(0)),
        Gen.constant(Val.Real(1)),
        Gen.constant(Val.Real(-1)),
        // Generate rationals with a constant denominator of 4. This should
        // give nice counterexamples with no decimal conversion error.
        Gen.rational32(Range.linearFrom(0, -10000, 10000), Range.constant(4, 4)).map(Val.Real(_))
      )

  def niceInts(minInclusive: num.Integer, maxInclusive: num.Integer): Gen[num.Integer] =
    val nice = List(0, 1, 2, 3, 4, 5, 12, 123, 255, 1234, 12345, 65535, 123456, 1234567, 12345678, 123456789, 1234567890)
    val range = nice.flatMap(n => List(n, -n)).filter(n => minInclusive <= n && n <= maxInclusive)
    Gen.elementIndexed(range.toIndexedSeq).map(n => num.Integer(n))


  def list(sorts: List[Sort]): Gen[List[Val]] =
    hedgehog.predef.sequence(sorts.map(value))

  def heap(env: Check.Env): Gen[Eval.Heap] =
    for
      vs <- list(env.values.toList)
    yield
      scala.collection.immutable.SortedMap.from(env.keys.zip(vs))
