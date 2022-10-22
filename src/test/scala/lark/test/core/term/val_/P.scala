package lark.test.core.term.val_

import lark.meta.base.{num, pretty}
import lark.meta.core.term
import lark.meta.core.term.Val
import lark.meta.core.Sort

import lark.test.hedgehog._
import lark.test.suite.HedgehogSuite

class P extends HedgehogSuite:

  for s <- Sort.Table.all do
    property(s"sort '${s.pprString}' generated value matches sort") {
      for
        value <- G.value(s).ppr("value")
      yield
        Result.assert(Val.check(value, s))
    }
