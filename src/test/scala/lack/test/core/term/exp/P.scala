package lack.test.core.term.exp

import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Eval
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.Sort

import lack.test.hedgehog._
import lack.test.suite._

class P extends HedgehogSuite:
  val g = G(lack.test.core.term.prim.G())

  property("generated expressions typecheck") {
    for
      env <- lack.test.core.sort.G.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s <- lack.test.core.sort.G.all.ppr("sort")
      e <- g.exp(env, s).ppr("expr")
      ppr <- Gen.constant(e.pprString).ppr("e.ppr")
    yield
      assertEquals(Check.exp(env, e, Check.Options()), s)
  }

  property("generated expressions eval OK (refines disabled)") {
    for
      env <- lack.test.core.sort.G.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s <- lack.test.core.sort.G.all.ppr("sort")
      e <- g.exp(env, s).ppr("expr")
      heap <- lack.test.core.term.val_.G.heap(env).ppr("heap")
      v <- Property.ppr(Eval.exp(heap, e, Eval.Options(checkRefinement = false)), "v")
    yield
      Result.assert(v.sort == s)
  }

  property("generated expressions eval OK (refines enabled & discarded)") {
    for
      env <- lack.test.core.sort.G.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s <- lack.test.core.sort.G.all.ppr("sort")
      e <- g.exp(env, s).ppr("e")
      heap <- lack.test.core.term.val_.G.heap(env).ppr("heap")

      v <- Property.try_ {
        Eval.exp(heap, e, Eval.Options(checkRefinement = true))
      }.ppr("v")
    yield
      Result.assert(Val.check(v, s))
  }