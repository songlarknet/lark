package lack.meta.core.term.val_

import lack.meta.core.term.Val
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

object G:
  def sort(sort: Sort): Gen[Val] = sort match
    case Sort.Bool =>
      Gen.boolean.map(Val.Bool(_))
    case Sort.ArbitraryInteger =>
      Gen.integer(Range.constant(Long.MinValue, Long.MaxValue))
        .map(Val.Int(_))
    case s: Sort.BoundedInteger =>
      Gen.integer(Range.constant(s.minInclusive, s.maxInclusive))
        .map(i => Val.Refined(s, Val.Int(i)))

    case Sort.Real =>
      Gen.rational32.map(Val.Real(_))

  def sorts(sorts: List[Sort]): Gen[List[Val]] =
    hedgehog.predef.sequence(sorts.map(sort))
