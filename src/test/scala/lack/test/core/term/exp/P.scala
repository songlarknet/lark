package lack.test.core.term.exp

import lack.meta.core.term
import lack.meta.core.term.Bounded
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

  property("raw.runtime expressions are bounded-precision") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s   <- g.sort.runtime.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
    yield
      assertEquals(Bounded.bound(e).repr, s)
  }

  property("if e bounded, then Bounded(e).annotated.sort is e.sort") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s   <- g.sort.runtime.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
      eB   = Bounded.bound(e)
      _   <- Property.ppr(eB.annotated, "Bounded(e).annotated")
    yield
      Result.diff(eB.annotated.sort, s)(_ == _)
  }

  property("if e bounded, then Bounded(e).annotated typechecks ok") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s   <- g.sort.runtime.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
      eB   = Bounded.bound(e)
      _   <- Property.ppr(eB.annotated, "Bounded(e).annotated")
    yield
      Result.diff(Check.exp(env, eB.annotated, Check.Options()), s)(_ == _)
  }

  property("if e bounded, then Bounded(e).original typechecks ok") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s   <- g.sort.runtime.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
      eB   = Bounded.bound(e)
      _   <- Property.ppr(eB.original, "Bounded(e).original")
    yield
      val ss = Check.exp(env, eB.original, Check.Options())
      assert(ss == s || (s.isInstanceOf[Sort.BoundedInteger] && ss.isInstanceOf[Sort.ArbitraryInteger.type]))
  }

  property("Bounded(e).annotated preserves value (refines disabled)") {
    for
      env <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s   <- g.sort.runtime.all.ppr("sort")
      e   <- g.raw(env, s).ppr("expr")
      eB   = Bounded.bound(e)
      _   <- Property.ppr(eB.annotated, "Bounded(e).annotated")
      heap <- g.val_.heap(env).ppr("heap")
      v    <- Property.ppr(Eval.exp(heap, e, Eval.Options(checkRefinement = false)), "v")
      vB   <- Property.ppr(Eval.exp(heap, eB.annotated, Eval.Options(checkRefinement = false)), "vB")
    yield
      Result.diff(vB, v)(_ == _)
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

  property("Compound.simp preserves boundedness (refines discarded)") {
    for
      env   <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      sort  <- g.sort.runtime.all.ppr("sort")
      raw   <- g.raw(env, sort).ppr("raw")
      simp  <- Property.ppr(term.Compound.simp.descend(raw), "simp")

      // Discard any tests with invalid values like u8'-1.
      heap  <- g.val_.heap(env).ppr("heap")
      _ <- Property.try_ {
        Eval.exp(heap, raw, Eval.Options(checkRefinement = true))
      }.ppr("v")
    yield
      assertEquals(Bounded.bound(simp).repr, Bounded.bound(raw).repr)
  }