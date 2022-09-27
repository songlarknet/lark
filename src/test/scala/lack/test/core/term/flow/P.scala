package lack.test.core.term.flow

import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Eval
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.Sort

import lack.test.hedgehog._
import lack.test.suite._

class P extends HedgehogSuite:
  val g = G(lack.test.core.term.exp.G(lack.test.core.term.prim.G()))

  property("generated flow expressions typecheck") {
    for
      env <- g.sort.env(Range.linear(1, 10), g.sort.all).ppr("env")
      previous <- g.sort.subenv(env).ppr("previous")
      s <- g.sort.all.ppr("sort")
      e <- g.flow(env, previous, s).ppr("expr")
    yield
      assertEquals(Check.flow(env, e, Check.Options()), s)
  }
