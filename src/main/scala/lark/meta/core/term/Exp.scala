package lark.meta.core.term

import lark.meta.base.num
import lark.meta.base.num.Integer
import lark.meta.base.{names, pretty}
import lark.meta.core.Sort
import lark.meta.core.term.prim.Table
import lark.meta.core.term.prim.Table.{Precedence => Prec}

/** Pure expressions */
sealed trait Exp extends pretty.Pretty:
  // Annotate each node with its type. Is this overkill? The expressions probably won't be "too big"...
  def sort: Sort

  def pprWith(showBoundedArith: Boolean = true, precedence: Int = Prec.PARENS_PREC): pretty.Doc
  def ppr = pprWith(showBoundedArith = true)

object Exp:
  /** Variable */
  case class Var(sort: Sort, v: names.Ref) extends Exp:
    def pprWith(showBoundedArith: Boolean, precedence: Int) = v.ppr

  /** Value */
  case class Val(v: lark.meta.core.term.Val) extends Exp:
    def sort = v.sort
    def pprWith(showBoundedArith: Boolean, precedence: Int) =
      if showBoundedArith
      then v.ppr
      else lark.meta.core.term.Val.unwrap(v).ppr

  /** Pure primitive application */
  case class App(sort: Sort, prim: Prim, args: Exp*) extends Exp:
    def pprWith(showBoundedArith: Boolean, precedence: Int) =
      (prim, args) match
        case (Table.Not, Seq(App(_, Table.Eq, arg1, arg2))) =>
          val (o, pp) = Prec.binop(Table.Eq).get
          pretty.precedence(precedence, pp,
            arg1.pprWith(showBoundedArith, pp) <+> pretty.text("!=") <+> arg2.pprWith(showBoundedArith, pp - 1))
        case (_, Seq(arg1)) if Prec.unop(prim).isDefined =>
          val (o, pp) = Prec.unop(prim).get
          pretty.precedence(precedence, pp,
            pretty.text(o) <> arg1.pprWith(showBoundedArith, pp - 1))
        case (_, Seq(arg1, arg2)) if Prec.binop(prim).isDefined =>
          val (o, pp) = Prec.binop(prim).get
          pretty.precedence(precedence, pp,
            arg1.pprWith(showBoundedArith, pp) <+> pretty.text(o) <+> arg2.pprWith(showBoundedArith, pp - 1))
        case (Table.Ite, Seq(p, t, f)) =>
          pretty.precedence(precedence, Prec.TERNARY_PREC,
            pretty.text("if") <+> p.pprWith(showBoundedArith, Prec.TERNARY_PREC - 1) <+>
            pretty.text("then") <+> t.pprWith(showBoundedArith, Prec.TERNARY_PREC - 1) <+>
            pretty.text("else") <+> f.pprWith(showBoundedArith, Prec.TERNARY_PREC))

        case (p, args) =>
          prim.ppr <> pretty.tupleP(args)

  /** A cast between two variables with different representation types but the
   * same logical type, eg UInt8 -> UInt32. */
  case class Cast(op: Cast.Op, e: Exp) extends Exp:
    def sort = op match
      case Cast.Box(r) => r
      case Cast.Unbox(r) => r

    def pprWith(showBoundedArith: Boolean, precedence: Int) =
      if showBoundedArith
      then op.ppr <> pretty.parens(e.pprWith(showBoundedArith, Prec.PARENS_PREC))
      else e.pprWith(showBoundedArith, precedence)

  object Cast:
    sealed trait Op extends pretty.Pretty
    case class Box(sort: Sort.Refinement) extends Op:
      def ppr = pretty.text("#bounded'") <> sort.valuePrefix
    case class Unbox(sort: Sort) extends Op:
      def ppr = pretty.text("#logical")
