package lack.meta.core.term.val_

import lack.meta.base.{num, pretty}
import lack.meta.core.term
import lack.meta.core.term.Val
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._
import lack.meta.test.suite.HedgehogSuite

class P extends HedgehogSuite:

  for s <- Sort.Table.base do
    property(s"val gen matches sort ${s.pprString}") {
      for
        value <- G.sort(s).log("value")
      yield
        Result.assert(value.check(s))
    }
