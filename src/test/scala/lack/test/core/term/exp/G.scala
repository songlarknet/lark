package lack.test.core.term.exp

import lack.meta.base.num
import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.Sort

import lack.test.hedgehog._

/** Generators for pure expressions */
case class G(primG: lack.test.core.term.prim.G):
  val sort = lack.test.core.sort.G
  val val_ = lack.test.core.term.val_.G

  /** Generate an expression of given type, with given environment.
   *
   * Tries to generate a primitive application that returns given sort
   */
  def exp(env: Check.Env, sort: Sort): Gen[Exp] =
    interesting(env, sort).rarely(arbitrary(env, sort))

  /** Generate an "interesting" expression of given type, with given environment.
   *
   * Tries to generate a primitive application or if-then-elses
   */
  def interesting(env: Check.Env, sort: Sort): Gen[Exp] = sort match
    case s: Sort.BoundedInteger =>
      Gen.choice1(
        prim(env, sort).rarely(ite(env, sort)),
        for
          e <- interesting(env, Sort.ArbitraryInteger)
        yield Exp.Cast(Exp.Cast.Box(s), e))
    case _ =>
      prim(env, sort).rarely(ite(env, sort))

  /** Generate an arbitrary expression of given type without worrying about
   * whether it's representative of a real program. */
  def arbitrary(env: Check.Env, sort: Sort): Gen[Exp] = sort match
    case Sort.Bool =>
      Gen.choice1(
        varCast(env, sort),
        value(sort),
        prim(env, sort)
      )
    case Sort.ArbitraryInteger =>
      Gen.choice1(
        varCast(env, sort),
        value(sort),
        prim(env, sort),
        unbox(env, sort)
      )
    case s: Sort.BoundedInteger =>
      Gen.choice1(
        varCast(env, sort),
        value(sort),
        prim(env, sort),
        box(env, s)
      )
    case Sort.Real =>
      Gen.choice1(
        varCast(env, sort),
        value(sort),
        prim(env, sort)
      )

  /** Generate constant value of given sort */
  def value(sort: Sort): Gen[Exp] =
    for
      v <- val_.value(sort)
    yield Exp.Val(sort, v)

  /** Generate a primitive application that returns given sort */
  def prim(env: Check.Env, s: Sort): Gen[Exp] =
    for
      (p,argsT) <- primG.result(s)
      argsV <- args(env, argsT)
    yield Exp.App(s, p, argsV : _*)

  /** Generate unique-ish simple arguments for given sorts */
  def args(env: Check.Env, sorts: List[Sort]): Gen[List[Exp]] =
    Gen.tryUniques(
      seeds = sorts
    )(
      main = varCast(env, _)
    )(
      fallback = { s => value(s).rarely(exp(env, s)) },
    )

  /** Generate an if-then-else chain with distinct predicates and terms */
  def ite(env: Check.Env, s: Sort): Gen[Exp] =
    def go(pts: List[(Exp, Exp)]): Gen[Exp] = pts match
      case Nil => varCast(env, s)
      case List((p,t)) => Gen.constant(t)
      case (p,t) :: pts =>
        for
          f <- go(pts)
        yield
          Exp.App(s, term.prim.Table.Ite, p, t, f)
    for
      n <- Gen.int(Range.linear(1, 5))
      ts <- args(env, List.fill(n)(s))
      ps <- args(env, List.fill(n)(Sort.Bool))
      e  <- go(ps.distinct.zip(ts.distinct))
    yield e

  def unbox(env: Check.Env, s: Sort): Gen[Exp] =
    for
      r <- sort.runtime.ints
      e <- arbitrary(env, r)
    yield Exp.Cast(Exp.Cast.Unbox(s), e)

  def box(env: Check.Env, s: Sort.Refinement): Gen[Exp] =
    for
      e <- arbitrary(env, Sort.ArbitraryInteger)
    yield Exp.Cast(Exp.Cast.Box(s), e)

  /** Cast given expression to Sort.ArbitraryInteger */
  def castToInteger(e: Exp): Gen[Exp] = e.sort match
    case Sort.Bool =>
      for
        vt <- value(Sort.ArbitraryInteger)
        vf <- value(Sort.ArbitraryInteger).ensure(_ != vt)
      yield
        compound.ite(e, vt, vf)
    case Sort.ArbitraryInteger =>
      Gen.constant(e)
    case s: Sort.BoundedInteger =>
      Gen.constant(Exp.Cast(Exp.Cast.Unbox(Sort.ArbitraryInteger), e))
    case Sort.Real =>
      for
        eb <- castToBool(e)
        ei <- castToInteger(eb)
      yield ei

  /** Cast given expression to bool */
  def castToBool(e: Exp): Gen[Exp] = e.sort match
    case Sort.Bool =>
      Gen.constant(e)
    case Sort.ArbitraryInteger =>
      for
        op <- compound.cmps
        z <- value(Sort.ArbitraryInteger)
      yield
        Exp.App(Sort.Bool, op, e, z)
    case s: Sort.BoundedInteger =>
      for
        ei <- castToInteger(e)
        eb <- castToBool(ei)
      yield eb
    case Sort.Real =>
      for
        op <- compound.cmps
        z <- value(Sort.Real)
      yield
        Exp.App(Sort.Bool, op, e, z)

  /** Look in environment for given sort, or `otherwise` if there are no variables
   * of given type in the environment.
   * If there is only one variable of the given type, then this will always
   * choose that variable. */
  def var_(env: Check.Env, sort: Sort, otherwise: Gen[Exp]): Gen[Exp] =
    val xs = env.filter(_._2 == sort)
    if xs.isEmpty
    then
      otherwise
    else
      for (x,s) <- Gen.elementUnsafe(xs.toList)
      yield Exp.Var(s, x)

  /** Use variable from environment, perhaps casting from variable type to
   * desired type.
   */
  def varCast(env: Check.Env, sort: Sort): Gen[Exp] =
    val fallback = var_(env, sort, otherwise = value(sort))
    val envX = env.map((k,v) => Exp.Var(v, k)).toIndexedSeq

    sort match
      case _ if env.isEmpty =>
        fallback
      case Sort.Bool =>
        for
          v <- Gen.elementIndexed(envX)
          e <- castToBool(v)
        yield e
      case Sort.ArbitraryInteger =>
        for
          v <- Gen.elementIndexed(envX)
          e <- castToInteger(v)
        yield e
      case s: Sort.BoundedInteger =>
        for
          v <- Gen.elementIndexed(envX)
          e <-
            if v.sort == s
            then Gen.constant(v)
            else castToInteger(v).map(Exp.Cast(Exp.Cast.Box(s), _))
        yield
          e
      case Sort.Real =>
        for
          v <- Gen.elementIndexed(envX)
          e <-
            if v.sort == sort
            then Gen.constant(v)
            else fallback
        yield
          e

  object compound:
    def vi(i: num.Integer): Exp.Val = Exp.Val(Sort.ArbitraryInteger, Val.Int(i))
    def vr(i: num.Real): Exp.Val = Exp.Val(Sort.Real, Val.Real(i))
    def ite(p: Exp, t: Exp, f: Exp) = Exp.App(t.sort, term.prim.Table.Ite, p, t, f)

    val cmps: Gen[term.Prim] = {
      import term.prim.Table._
      Gen.element1(
        Eq, Lt, Le, Gt, Ge
      )
    }
