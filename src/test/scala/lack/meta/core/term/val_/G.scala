package lack.meta.core.term.val_

import lack.meta.core.term.Val
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

object G:
  def sort(sort: Sort): Gen[Val] = sort match
    case Sort.Bool =>
      Gen.boolean.map(Val.Bool(_))
    case s: Sort.Integral =>
      Gen.integer(Range.constant(s.minInclusive, s.maxInclusive))
        .map(Val.Int(_))

    case Sort.Real32 =>
      Gen.rational32.map(Val.Real(_))
