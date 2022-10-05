package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.Sort

/** Streaming terms */
sealed trait Flow extends pretty.Pretty:
  def sort: Sort
object Flow:
  /** Pure expression */
  case class Pure(e: Exp) extends Flow:
    def ppr  = e.ppr
    def sort = e.sort

  /** x -> y, or "first x then y". */
  case class Arrow(a: Exp, b: Exp) extends Flow:
    def sort = a.sort
    def ppr = pretty.sexpr(List("->", a.ppr, b.ppr))

  /** Followed by, or initialised delay.
   * Fby(v, e) or in Lustre syntax "v fby e" is equivalent to
   * "v -> pre e". */
  case class Fby(v: Val, e: Exp) extends Flow:
    def sort = e.sort
    def ppr  = pretty.sexpr(List("fby", v.ppr, e.ppr))

  /** Previous value.
   * Pre(e) is equivalent to Fby(undefined, e) for some fresh undefined
   * value.
   * Having this as a separate primitive might make pretty-printing a little
   * bit nicer, but I'm not sure whether it's worth it.
   */
  case class Pre(e: Exp) extends Flow:
    def sort = e.sort
    def ppr  = pretty.sexpr(List("pre", e.ppr))

  def app(prim: Prim, args: Exp*) =
    Flow.Pure(Compound.app(prim, args : _*))
  def var_(sort: Sort, v: names.Ref) =
    Flow.Pure(Exp.Var(sort, v))
  def val_(v: Val) =
    Flow.Pure(Exp.Val(v))
