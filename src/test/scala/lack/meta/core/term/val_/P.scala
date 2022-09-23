package lack.meta.core.term.val_

import lack.meta.base.{num, pretty}
import lack.meta.core.term
import lack.meta.core.term.Val
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._
import lack.meta.test.suite.HedgehogSuite

class P extends HedgehogSuite:

  for s <- Sort.Table.all do
    property(s"sort '${s.pprString}' generated value matches sort") {
      for
        value <- G.sort(s).log("value")
      yield
        Result.assert(Val.check(value, s))
    }
