package lack.test.core.term.prim

import lack.meta.base.pretty
import lack.meta.core
import lack.meta.core.term.{Prim, Val}
import lack.meta.core.term.prim.Table
import lack.meta.core.Sort

import lack.test.hedgehog._
import lack.test.suite.HedgehogSuite

/** Properties for primitives */
class P extends HedgehogSuite:
  val g = G()
  val val_ = lack.test.core.term.val_.G

  test("prim table complete") {
    val missing = Table.base.filter { p =>
      !g.lookup.contains(p)
    }

    assertEquals(missing, List())
  }

  for (p <- g.table) {
    property(s"prim '${p.prim.pprString}' generate args") {
      for
        args <- p.args().ppr("args")
        r = p.prim.sort(args)
      yield
        Result.success
    }

    property(s"prim '${p.prim.pprString}' generate args for result") {
      for
        r  <- G.sort.all.ppr("r")
        ok <-
          p.args(r) match
            case None => Property.point(Result.Success)
            case Some(argsG) =>
              for
                args <- argsG.ppr("args")
                r2    = p.prim.sort(args)
              yield
                Result.diff(r, r2)(_ == _)
      yield ok
    }

    property(s"prim '${p.prim.pprString}' generate partial application") {
      for
        partial <- G.sort.all.list(Range.linear(0, 3)).ppr("partial")
        ok <-
          p.partial(partial) match
            case None => Property.point(Result.Success)
            case Some(suffixG) =>
              for
                suffix <- suffixG.ppr("suffix")
                r2      = p.prim.sort(partial ++ suffix)
              yield
                Result.success
      yield ok
    }

    property(s"prim '${p.prim.pprString}' args eval") {
      for
        sorts      <- p.args().ppr("sorts")
        values     <- val_.list(sorts).ppr("values")
        resultSort <- Property.ppr(p.prim.sort(sorts), "resultSort")
        result     <- Property.ppr(p.prim.eval(values), "result")
      yield
        Result.assert(Val.check(result, resultSort))
    }
  }
