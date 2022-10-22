package lark.test.core.term.flow

import lark.meta.core.term
import lark.meta.core.term.Check
import lark.meta.core.term.Eval
import lark.meta.core.term.Exp
import lark.meta.core.term.Val
import lark.meta.core.Sort

import lark.test.hedgehog._
import lark.test.suite._

class P extends HedgehogSuite:
  val g = G(lark.test.core.term.exp.G(lark.test.core.term.prim.G()))

  property("generated flow expressions typecheck") {
    for
      env <- g.sort.env(Range.linear(1, 10), g.sort.all).ppr("env")
      previous <- g.sort.subenv(env).ppr("previous")
      s <- g.sort.all.ppr("sort")
      e <- g.flow(env, previous, s).ppr("expr")
    yield
      assertEquals(Check.flow(env, e, Check.Options()), s)
  }
