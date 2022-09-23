package lack.meta.core.term.prim

import lack.meta.base.pretty
import lack.meta.core
import lack.meta.core.term.{Prim, Val}
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._
import lack.meta.test.suite._

/** Properties for primitives */
class P extends lack.meta.test.suite.HedgehogSuite:
  val g = G()

  test("prim table complete") {
    val missing = Table.base.filter { p =>
      !g.lookup.contains(p)
    }

    assertEquals(missing, List())
  }

  for (p <- g.table) {
    property(s"prim '${p.prim.pprString}' generate args") {
      for
        args <- p.args().log("args")
        r = p.prim.sort(args)
      yield
        ()
    }

    property(s"prim '${p.prim.pprString}' generate args for result") {
      for
        r  <- core.sort.G.all.log("r")
        ok <-
          p.args(r) match
            case None => Property.point(Result.Success)
            case Some(argsG) =>
              for
                args <- argsG.log("args")
                r2    = p.prim.sort(args)
              yield
                Result.diff(r, r2)(_ == _)
      yield ok
    }

    property(s"prim '${p.prim.pprString}' generate partial application") {
      for
        partial <- core.sort.G.all.list(Range.linear(0, 3)).log("partial")
        ok <-
          p.partial(partial) match
            case None => Property.point(Result.Success)
            case Some(suffixG) =>
              for
                suffix <- suffixG.log("suffix")
                r2      = p.prim.sort(partial ++ suffix)
              yield
                Result.success
      yield ok
    }

    property(s"prim '${p.prim.pprString}' args eval") {
      for
        sorts     <- p.args().log("sorts")
        values    <- core.term.val_.G.sorts(sorts).log("values")
        resultSort = p.prim.sort(sorts)
        result     = p.prim.eval(values)
      yield
        Result.assert(Val.check(result, resultSort))
          .log(s"resultSort: ${resultSort.pprString}")
          .log(s"result: ${result.pprString}")
    }
  }

  // TODO: props
  // evaluation is sound: matches types
  // evaluation matches smt
