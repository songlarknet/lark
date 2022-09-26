package lack.meta.core.term.exp

import lack.meta.base.num
import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.sort
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

case class G(primG: term.prim.G):
  /** variable lookup, or literal value if no variable matches desired sort */
  def var_(env: Check.Env, sort: Sort, otherwise: Gen[Exp]): Gen[Exp] =
    val xs = env.filter(_._2 == sort)
    if xs.isEmpty
    then
      otherwise
    else
      for (x,s) <- Gen.elementUnsafe(xs.toList)
      yield Exp.Var(s, x)

  def val_(sort: Sort): Gen[Exp] =
    for
      v <- term.val_.G.sort(sort)
    yield Exp.Val(sort, v)

  /** try to generate a list of unique expressions, but don't try _too_ hard */
  def uniqueExpressions(gen: Sort => Gen[Exp], fallback: Sort => Gen[Exp], sorts: List[Sort], args: List[Exp] = List()): Gen[List[Exp]] = sorts match
    case Nil => Gen.constant(args.reverse)
    case s :: sortsX =>
      for
        e  <- gen(s)
        eX <-
          if args.contains(e)
          then fallback(s) else Gen.constant(e)
        rest <- uniqueExpressions(gen, fallback, sortsX, eX :: args)
      yield rest

  def prim(env: Check.Env, s: Sort): Gen[Exp] =
    for
      (p,argsT) <- primG.result(s)
      argsV <- uniqueExpressions(
        gen = var_try_hard(env, _),
        fallback = { s => Gen.choice1(val_(s), val_(s), exp(env, s)) },
        sorts = argsT
      )
    yield Exp.App(s, p, argsV : _*)

  def unbox(env: Check.Env, s: Sort): Gen[Exp] =
    for
      r <- sort.G.runtime.ints
      e <- exp(env, r)
    yield Exp.Cast(Exp.Cast.Unbox(s), e)

  def box(env: Check.Env, s: Sort.Refinement): Gen[Exp] =
    for
      e <- exp(env, Sort.ArbitraryInteger)
    yield Exp.Cast(Exp.Cast.Box(s), e)

  /** */
  def exp(env: Check.Env, sort: Sort): Gen[Exp] = sort match
    case Sort.Bool =>
      Gen.choice1(
        var_try_hard(env, sort),
        // val_(sort),
        // var_(env, sort, otherwise = val_(sort)),
        prim(env, sort)
      )
    case Sort.ArbitraryInteger =>
      Gen.choice1(
        var_try_hard(env, sort),
        // val_(sort),
        // var_(env, sort, otherwise = val_(sort)),
        prim(env, sort),
        // unbox(env, sort)
      )
    case s: Sort.BoundedInteger =>
      Gen.choice1(
        var_try_hard(env, sort),
        // val_(sort),
        // var_(env, sort, otherwise = val_(sort)),
        prim(env, sort),
        box(env, s)
      )
    case Sort.Real =>
      Gen.choice1(
        var_try_hard(env, sort),
        // val_(sort),
        // var_(env, sort, otherwise = val_(sort)),
        prim(env, sort)
      )

  /** try to construct idiomatic expressions that look a bit more like real
   * programs */
  def var_try_hard(env: Check.Env, sort: Sort): Gen[Exp] =
    def vi(i: num.Integer): Exp.Val = Exp.Val(Sort.ArbitraryInteger, Val.Int(i))
    def vr(i: num.Real): Exp.Val = Exp.Val(Sort.Real, Val.Real(i))
    def ite(p: Exp, t: Exp, f: Exp) = Exp.App(t.sort, term.prim.Table.Ite, p, t, f)

    val cmps: Gen[term.Prim] = {
      import term.prim.Table._
      Gen.element1(
        Eq, Lt, Le, Gt, Ge
      )
    }

    def castToInteger(e: Exp): Gen[Exp] = e.sort match
      case Sort.Bool =>
        for
          vt <- val_(Sort.ArbitraryInteger)
          vf <- val_(Sort.ArbitraryInteger).ensure(_ != vt)
        yield
          ite(e, vt, vf)
      case Sort.ArbitraryInteger =>
        Gen.constant(e)
      case s: Sort.BoundedInteger =>
        Gen.constant(Exp.Cast(Exp.Cast.Unbox(Sort.ArbitraryInteger), e))
      case Sort.Real =>
        for
          eb <- castToBool(e)
          ei <- castToInteger(eb)
        yield ei

    def castToBool(e: Exp): Gen[Exp] = e.sort match
      case Sort.Bool =>
        Gen.constant(e)
      case Sort.ArbitraryInteger =>
        for
          op <- cmps
          z <- val_(Sort.ArbitraryInteger)
        yield
          Exp.App(Sort.Bool, op, e, z)
      case s: Sort.BoundedInteger =>
        for
          ei <- castToInteger(e)
          eb <- castToBool(ei)
        yield eb
      case Sort.Real =>
        for
          op <- cmps
          z <- val_(Sort.Real)
        yield
          Exp.App(Sort.Bool, op, e, z)

    val envX = env.map((k,v) => Exp.Var(v, k)).toIndexedSeq

    def var_otherwise(s: Sort): Gen[Exp] = s match
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
      case _ =>
        val_(s)

    sort match
      case Sort.Bool =>
        var_otherwise(sort)
        // var_(env, sort, otherwise = var_otherwise(sort))
      case Sort.ArbitraryInteger =>
        var_otherwise(sort)
        // var_(env, sort, otherwise = var_otherwise(sort))
      case s: Sort.BoundedInteger =>
        var_(env, sort, otherwise = (for
          e <- var_otherwise(s.logical)
        yield Exp.Cast(Exp.Cast.Box(s), e)))
      case Sort.Real =>
        var_(env, sort, otherwise = var_otherwise(sort))
