package lack.meta.core.term.val_

import lack.meta.base.num
import lack.meta.core.term.Eval
import lack.meta.core.term.Check
import lack.meta.core.term.Val
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

object G:
  def sort(sort: Sort): Gen[Val] = sort match
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
      def rf(i: lack.meta.base.num.Integer) = Val.Refined(s, Val.Int(i))
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
        Gen.rational32(Range.linearFrom(0, -10000, 10000), Range.constant(10, 10)).map(Val.Real(_))
      )

  def niceInts(minInclusive: num.Integer, maxInclusive: num.Integer): Gen[num.Integer] =
    val nice = List(0, 1, 2, 3, 4, 5, 12, 123, 255, 1234, 12345, 65535, 123456, 1234567, 12345678, 123456789, 1234567890)
    val range = nice.flatMap(n => List(n, -n)).filter(n => minInclusive <= n && n <= maxInclusive)
    Gen.elementIndexed(range.toIndexedSeq).map(n => num.Integer(n))


  def sorts(sorts: List[Sort]): Gen[List[Val]] =
    hedgehog.predef.sequence(sorts.map(sort))

  def heap(env: Check.Env): Gen[Eval.Heap] =
    for
      vs <- sorts(env.values.toList)
    yield
      scala.collection.immutable.SortedMap.from(env.keys.zip(vs))
