package lack.meta.core.term.flow

import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Eval
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.sort
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._
import lack.meta.test.suite._

class P extends HedgehogSuite:
  val g = G(term.exp.G(term.prim.G()))

  property("generated flow expressions typecheck") {
    for
      env <- sort.G.env(Range.linear(1, 10), sort.G.all).ppr("env")
      previous <- sort.G.subenv(env).ppr("previous")
      s <- sort.G.all.ppr("sort")
      e <- g.flow(env, previous, s).ppr("expr")
    yield
      assertEquals(Check.flow(env, e, Check.Options()), s)
  }
