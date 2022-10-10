package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core.Sort

/** Logical representation of values */
sealed trait Val extends pretty.Pretty:
  def sort: Sort

object Val:
  /** Boolean values. */
  case class Bool(b: Boolean) extends Val:
    def ppr = pretty.text(if (b) "#b'true" else "#b'false")
    def sort = Sort.Bool

  /** Unbounded integer values.
   *
   * Operations on these use unbounded arithmetic, at least conceptually,
   * but to compile these operations we need to prove that they don't
   * overflow the runtime representation type. */
  case class Int(i: Integer) extends Val:
    def ppr = pretty.value(i)
    def sort = Sort.ArbitraryInteger

  /** Mathematical real number.
   *
   * These values are logically reals, but the compiled runtime
   * representation is a float, which is a bit of a lie. */
  case class Real(r: num.Real) extends Val:
    def ppr = pretty.value(r.toDouble)
    def sort = Sort.Real

  /** Boxed values that satisfy some predicate. */
  case class Refined(s: Sort.Refinement, v: Val) extends Val:
    def ppr = pretty.hash <> s.valuePrefix <> pretty.squote <> v.ppr
    def sort = s

  /** Check if a value matches a sort and satisfies the refinement predicate
   * if there is one. */
  def check(v: Val, sort: Sort, checkRefinement: Boolean = true): Boolean =
    v.sort == sort &&
      (v match
        case Refined(r, v) if checkRefinement => r.refinesVal(v)
        case _ => true)

  /** Construct an arbitrary junk value for given sort. */
  def arbitrary(sort: Sort): Val = sort match
    case Sort.ArbitraryInteger => Val.Int(0)
    case Sort.Bool => Val.Bool(false)
    case Sort.Real => Val.Real(0.0)
    case s: Sort.BoundedInteger =>
      val v = if s.refinesVal(Val.Int(0))
              then Val.Int(0)
              else Val.Int(s.minInclusive)
      Val.Refined(s, v)

  /** Fake unit value */
  def unit = Val.Bool(false)

  /** Approximate equality for floats. This might not be necessary if we switch
   * Val.Real over to rationals.
   */
  def approx(v: Val, w: Val, eps: num.Real = 1e-20): Boolean = (v, w) match
    case _ if v == w => true
    case (Val.Real(i), Val.Real(j)) =>
      val diff = (i - j).abs
      val max  = i.abs.max(j.abs)
      val diffx= if max == 0 then eps else diff / max
      diffx.abs < eps || (i.abs < eps && j.abs < eps)
    case _ => false
