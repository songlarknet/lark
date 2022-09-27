package lack.meta.core.term.flow

import lack.meta.base.num
import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Exp
import lack.meta.core.term.Flow
import lack.meta.core.term.Val
import lack.meta.core.sort
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

/** Generators for pure expressions */
case class G(expG: term.exp.G):
  /** Generate a streaming expression of given type, with given environment.
   *
   * Takes two environments: "current" and "previous". The current environment
   * contains the variables that can be used in any expression, while the
   * previous environment can only be used in "pre" or "fby" contexts.
   * The current environment is usually a subset of the previous environment.
   */
  def flow(current: Check.Env, previous: Check.Env, sort: Sort): Gen[Flow] =
    Gen.choice1(
      for
        e <- expG.exp(current, sort)
      yield Flow.Pure(e),
      for
        e <- expG.exp(current, sort)
        f <- expG.exp(current, sort)
      yield Flow.Arrow(e, f),
      for
        v <- term.val_.G.sort(sort)
        e <- expG.exp(previous, sort)
      yield Flow.Fby(v, e),
      for
        e <- expG.exp(previous, sort)
      yield Flow.Pre(e))
