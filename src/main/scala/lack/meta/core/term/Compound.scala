package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.Sort

import scala.util.Try

object Compound:
  def var_(sort: Sort, v: names.Ref) =
    Exp.Var(sort, v)

  def val_(v: Val) = Exp.Val(v.sort, v)

  def app(prim: Prim, args: Exp*): Exp =
    Try(args.map(a => take.val_(a).get)).toOption match
      case Some(vs) =>
        val_(prim.eval(vs.toList))
      case None =>
        Exp.App(prim.sort(args.map(_.sort).toList), prim, args : _*)

  def unbox(exp: Exp): Exp =
    val op = Exp.Cast.Unbox(Sort.logical(exp.sort))
    exp match
      case Exp.Val(_, v) => val_(Eval.cast(op, v, Eval.Options()))
      case Exp.Cast(Exp.Cast.Box(_), e) => e
      case _ => Exp.Cast(op, exp)

  def box(refinement: Sort.Refinement, exp: Exp): Exp =
    val op = Exp.Cast.Box(refinement)
    exp match
      case Exp.Val(_, v) => val_(Eval.cast(op, v, Eval.Options()))
      case Exp.Cast(Exp.Cast.Unbox(_), e)
        if e.sort == refinement
        => e
      case _ => Exp.Cast(op, exp)


  def ite(p: Exp, t: Exp, f: Exp) =
    app(prim.Table.Ite, p, t, f)

  object take:
    def val_(exp: Exp): Option[Val] = exp match
      case Exp.Val(_, v) => Some(v)
      case _ => None
