package lack.meta.core.term

import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Static semantics of expressions and flow expressions. */
object Check:
  type Env = names.immutable.RefMap[Sort]

  /** Typechecking options.
   *
   * @param checkRefinement
   *  If false, do not check that values of refinement types satisfy the
   *  refinement predicate.
  */
  case class Options(
    checkRefinement: Boolean = true
  )

  def val_(v: Val, options: Options): Sort =
    if options.checkRefinement && !Val.check(v, v.sort) then
      throw new except.RefinementException(v.sort, v)
    v.sort

  /** Typecheck expressions under environment */
  def exp(env: Env, e: Exp, options: Options): Sort = e match
    case e @ Exp.Var(_, v) =>
      env.getOrElse(v,
        throw new except.NoSuchVariableException(e, env))
    case Exp.Val(_, v) =>
      val_(v, options)
    case Exp.App(expectT, p, args : _*) =>
      val argsT = args.map(exp(env, _, options)).toList
      val gotT  = p.sort(argsT)
      if gotT != expectT then
        throw new except.BadApplication(p, e, argsT, expectT, gotT)
      gotT
    case Exp.Cast(Exp.Cast.Box(s), e) =>
      val t = exp(env, e, options)
      if t != s.logical then
        throw new except.BadCastBox(s, e, t)
      s
    case Exp.Cast(Exp.Cast.Unbox(s), e) =>
      exp(env, e, options) match
        case r: Sort.Refinement if r.logical == s =>
          s
        case t =>
          throw new except.BadCastUnbox(s, e, t)

  /** Typecheck flow streaming expressions. */
  def flow(env: Env, flow: Flow, options: Options): Sort = flow match
    case Flow.Pure(e) =>
      exp(env, e, options)
    case Flow.Arrow(first, later) =>
      val s = exp(env, first, options)
      val t = exp(env, first, options)
      if s != t then
        throw new except.BadDifferentTypes(s, t)
      t

    case Flow.Fby(v, e) =>
      val s = val_(v, options)
      val t = exp(env, e, options)
      if s != t then
        throw new except.BadDifferentTypes(s, t)
      t

    case Flow.Pre(e) =>
      exp(env, e, options)

  object except:
    class CheckException(msg: String) extends Exception(msg)

    class NoSuchVariableException(e: Exp.Var, env: Env) extends CheckException(
      s"""No such variable ${e.v.pprString} with sort ${e.sort.pprString}.
        |Environment: ${names.Namespace.fromMap(env).pprString}""".stripMargin)

    class BadApplication(prim: Prim, e: Exp, args: List[Sort], expect: Sort, got: Sort) extends CheckException(
      s"""Tried to apply primitive ${prim.pprString} returns ${got.pprString}, expected ${expect.pprString}.
        |Argument types: ${pretty.layout(pretty.tupleP(args))}
        |Expression: ${e.pprString}""".stripMargin)

    class BadDifferentTypes(expect: Sort, got: Sort) extends CheckException(
      s"""Bad, got ${got.pprString} but expected ${expect.pprString}.""".stripMargin)

    class BadCastBox(s: Sort.Refinement, e: Exp, t: Sort) extends CheckException(
      s"""Can't box type ${t.pprString} to ${s.pprString}.
        |Logical type ${s.logical.pprString} != ${t.pprString}.
        |Expression: ${e.pprString}""".stripMargin)

    class BadCastUnbox(s: Sort, e: Exp, t: Sort) extends CheckException(
      s"""Can't unbox type ${t.pprString} to get ${s.pprString}.
        |Expression: ${e.pprString}""".stripMargin)

    class RefinementException(sort: Sort, v: Val) extends CheckException(
      s"""Value ${v.pprString} does not satisfy refinement type predicate.
        |Type: ${sort.pprString}.""".stripMargin)
