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

  property("raw expressions typecheck") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s   <- g.sort.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
      ppr <- Gen.constant(e.pprString).ppr("e.ppr")
    yield
      assertEquals(Check.exp(env, e, Check.Options()), s)
  }

  property("raw expressions eval OK (refines disabled)") {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s    <- g.sort.all.ppr("sort")
      e    <- g.raw(env, s).ppr("expr")
      heap <- g.val_.heap(env).ppr("heap")
      v    <- Property.ppr(Eval.exp(heap, e, Eval.Options(checkRefinement = false)), "v")
    yield
      Result.assert(v.sort == s)
  }

  property("raw expressions eval OK (refines enabled & discarded)") {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      s    <- g.sort.all.ppr("sort")
      e    <- g.raw(env, s).ppr("e")
      heap <- g.val_.heap(env).ppr("heap")

      v <- Property.try_ {
        Eval.exp(heap, e, Eval.Options(checkRefinement = true))
      }.ppr("v")
    yield
      Result.assert(Val.check(v, s))
  }

  property("Compound.simp preserves types") {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      sort <- g.sort.all.ppr("sort")
      raw  <- g.raw(env, sort).ppr("raw")
      simp <- Property.ppr(term.Compound.simp.descend(raw), "simp")
      sortX<- Property.ppr(Check.exp(env, simp, Check.Options()), "simplified sort")
    yield
      assertEquals(sort, sortX)
  }

  property("Compound.simp preserves values") {
    for
      env   <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.all).ppr("env")
      sort  <- g.sort.all.ppr("sort")
      raw   <- g.raw(env, sort).ppr("raw")
      heap  <- g.val_.heap(env).ppr("heap")
      simp  <- Property.ppr(term.Compound.simp.descend(raw), "simp")
      rawV  <- Property.ppr(Eval.exp(heap, raw,  Eval.Options(checkRefinement = false)), "raw value")
      simpV <- Property.ppr(Eval.exp(heap, simp, Eval.Options(checkRefinement = false)), "simplified value")
    yield
      assertEquals(rawV, simpV)
  }