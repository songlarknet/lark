package lack.meta.core.term.exp

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
  val g = G(term.prim.G())

  property("generated expressions typecheck") {
    for
      env <- sort.G.env(Range.linear(1, 10), sort.G.all).log("env")
      s <- sort.G.all.log("sort")
      e <- g.exp(env, s).log("expr")
      ppr <- Gen.constant(e.pprString).log("e.ppr")
    yield
      assertEquals(Check.exp(env, e, Check.Options()), s)
  }

  property("generated expressions eval OK (refines disabled)") {
    for
      env <- sort.G.env(Range.linear(1, 10), sort.G.all).log("env")
      s <- sort.G.all.log("sort")
      e <- g.exp(env, s).log("expr")
      heap <- term.val_.G.heap(env).log("heap")
      _ <- Gen.constant(e.pprString).log("e.ppr")
      v = Eval.exp(heap, e, Eval.Options(checkRefinement = false))
    yield
      Result.assert(v.sort == s)
        .log(s"v: ${v.pprString}")
  }

  property("generated expressions eval OK (refines enabled & discarded)") {
    for
      env <- sort.G.env(Range.linear(1, 10), sort.G.all).log("env")
      s <- sort.G.all.log("sort")
      e <- g.exp(env, s).log("expr")
      heap <- term.val_.G.heap(env).log("heap")
      _ <- Gen.constant(e.pprString).log("e.ppr")

      vok <- Property.point(try {
        (Eval.exp(heap, e, Eval.Options(checkRefinement = true)), true)
      } catch {
        case e: Eval.except.RefinementException =>
          (Val.arbitrary(s), false)
      })

      v = vok._1
      ok = vok._2
      _ <- if !ok then Property.discard else Property.point(())
    yield
      Result.assert(Val.check(v, s))
        .log(s"v: ${v.pprString}")
  }