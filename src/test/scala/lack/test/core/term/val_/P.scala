package lack.test.core.term.val_

import lack.meta.base.{num, pretty}
import lack.meta.core.term
import lack.meta.core.term.Val
import lack.meta.core.Sort

import lack.test.hedgehog._
import lack.test.suite.HedgehogSuite

class P extends HedgehogSuite:

  for s <- Sort.Table.all do
    property(s"sort '${s.pprString}' generated value matches sort") {
      for
        value <- G.value(s).ppr("value")
      yield
        Result.assert(Val.check(value, s))
    }
