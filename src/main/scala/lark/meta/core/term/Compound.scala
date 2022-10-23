package lark.meta.core.term

import lark.meta.base.num
import lark.meta.base.num.Integer
import lark.meta.base.{names, pretty}
import lark.meta.core.Sort

import scala.util.Try

object Compound:
  def var_(sort: Sort, v: names.Ref) =
    Exp.Var(sort, v)

  def val_(v: Val) =
    Exp.Val(v)

  def app(prim: Prim, args: Exp*): Exp =
    simp.outer(Exp.App(prim.sort(args.map(_.sort).toList), prim, args : _*))

  def unbox(exp: Exp): Exp =
    simp.outer(Exp.Cast(Exp.Cast.Unbox(Sort.logical(exp.sort)), exp))

  def box(refinement: Sort.Refinement, exp: Exp): Exp =
    simp.outer(Exp.Cast(Exp.Cast.Box(refinement), exp))

  def ite(p: Exp, t: Exp, f: Exp) =
    app(prim.Table.Ite, p, t, f)

  def subst(env: names.immutable.RefMap[Exp], exp: Exp): Exp = exp match
    case Exp.Val(_) => exp
    case Exp.Var(_, v) => env.getOrElse(v, exp)
    case Exp.App(s, p, args : _*) =>
      simp.outer(Exp.App(s, p, args.map(subst(env, _)) : _*))
    case Exp.Cast(op, e) =>
      simp.outer(Exp.Cast(op, subst(env, e)))


  def subst(env: names.immutable.RefMap[Exp], flow: Flow): Flow = flow match
    case Flow.Pure(e)     => Flow.Pure(subst(env, e))
    case Flow.Pre(e)      => Flow.Pre(subst(env, e))
    case Flow.Fby(v, e)   => Flow.Fby(v, subst(env, e))
    case Flow.Arrow(f, l) => Flow.Arrow(subst(env, f), subst(env, l))

  object simp:
    /** Simplify outer-most layer of expression without descending into
     * the expression.
     * Performs constant propagations and removes spurious casts.
     * This is used by the smart constructors to ensure that they only do a
     * constant amount of work.
     */
    def outer(exp: Exp): Exp = exp match
      case Exp.App(s, prim.Table.Ite, Exp.Val(Val.Bool(p)), t, f) =>
        if p then t else f
      case Exp.App(s, prim, args : _*) =>
        Try(args.map(a => take.val_(a).get)).toOption match
          case Some(vs) =>
            val_(prim.eval(vs.toList))
          case None =>
            Exp.App(prim.sort(args.map(_.sort).toList), prim, args : _*)
      case Exp.Cast(op, Exp.Val(v)) =>
        // The cast will fail when the value does not satisfy the desired type,
        // for example, casting -1 to UInt32. In that case, we don't simplify
        // it at all so that the user can deal with this later.
        try
          val_(Eval.cast(op, v, Eval.Options()))
        catch
          case e: Eval.except.EvalException =>
            exp
      // XXX: this is logically fine, but it can remove precision information
      // needed to compile to C.
      // case Exp.Cast(Exp.Cast.Unbox(r), Exp.Cast(Exp.Cast.Box(_), e)) =>
      //   e
      case Exp.Cast(Exp.Cast.Box(r), Exp.Cast(Exp.Cast.Unbox(_), e))
        if e.sort == r =>
        e
      // case Exp.Cast(Exp.Cast.Box(r), Exp.Cast(Exp.Cast.Unbox(_), Exp.Cast(Exp.Cast.Box(rX), e)))
      //   if r.includes(rX) == Some(true) =>
      //   e
      case _ => exp

    /** Recursively simplify expression.
     * Performs constant propagations and removes spurious casts.
     */
    def descend(exp: Exp): Exp = exp match
      case Exp.App(s, prim, args : _*) =>
        outer(Exp.App(s, prim, args.map(descend(_)) : _*))
      case Exp.Cast(op, e) =>
        outer(Exp.Cast(op, descend(e)))
      case _ => exp

  object take:
    def val_(exp: Exp): Option[Val] = exp match
      case Exp.Val(v) => Some(v)
      case _ => None

    /** Take variables that occur in expression.
     * The term language doesn't include any binding forms, so the variables
     * returned are all free variables. */
    def vars(exp: Exp): Seq[Exp.Var] = exp match
      case v: Exp.Var => Seq(v)
      case _: Exp.Val => Seq()
      case Exp.App(s, p, args : _*) => args.flatMap(vars(_))
      case Exp.Cast(op, e) => vars(e)
