package lack.meta.core

import lack.meta.core.term.{Exp, Val, prim}
import lack.meta.base.names

import lack.meta.base.pretty
import lack.meta.base.num.{Integer, Range}

/** First-order types that represent sets of logical values or runtime
 * values. */
trait Sort extends pretty.Pretty

object Sort:
  /** Refinement types that restrict some logical set, eg bounded integers. */
  trait Refinement extends Sort:
    def valuePrefix: pretty.Doc
    def logical: Sort
    def refinesExp(v: Exp): Exp
    def refinesVal(v: Val): Boolean

  /** Get the logical representation of a set, eg logical(UInt32) = ArbitraryInteger */
  def logical(sort: Sort): Sort = sort match
    case r: Refinement => logical(r.logical)
    case _ => sort

  case object Bool extends Sort:
    def ppr = pretty.text("Bool")

  abstract class Numeric extends Sort

  /** Logical integers with arbitrary precision.
   * These are the logical representation of bounded integers.
   * These should not generally be used by users, because C compilation
   * will fail if they are used.
   */
  case object ArbitraryInteger extends Numeric:
    def ppr = pretty.text("Integer")

  /** Fixed-width integers with integer arithmetic.
    * Arithmetic overflow is not defined. */
  abstract class BoundedInteger(val width: Int, val signed: Boolean) extends Refinement:
    def ppr = pretty.text(if (signed) "Int" else "UInt") <> pretty.value(width)
    def valuePrefix = pretty.text(if (signed) "i" else "u") <> pretty.value(width)
    def minInclusive: Integer = if (signed) (Integer(-1) << (width - 1)) else 0
    def maxInclusive: Integer = (if (signed) (Integer(1) << (width - 1)) else (Integer(1) << width)) - 1

    def logical = ArbitraryInteger
    def refinesVal(v: Val) = v match
      case Val.Int(i) => minInclusive <= i && i <= maxInclusive
      case _          => false
    def refinesExp(v: Exp) =
      Exp.App(Bool, prim.Table.And,
        Exp.App(Bool, prim.Table.Le, Exp.Val(ArbitraryInteger, Val.Int(minInclusive)), v),
        Exp.App(Bool, prim.Table.Le, v, Exp.Val(ArbitraryInteger, Val.Int(maxInclusive))))

  case object Int8   extends BoundedInteger(8, true)
  case object UInt8  extends BoundedInteger(8, false)
  case object Int16  extends BoundedInteger(16, true)
  case object UInt16 extends BoundedInteger(16, false)
  case object Int32  extends BoundedInteger(32, true)
  case object UInt32 extends BoundedInteger(32, false)
  case object Int64  extends BoundedInteger(64, true)
  case object UInt64 extends BoundedInteger(64, false)

  /** A mathematical real number. Right now the runtime representation is a float32. */
  case object Real extends Numeric:
    def ppr = pretty.text("Real")

  /** Lists of sorts */
  object Table:
    /** Primitive sorts */
    object logical:
      val numeric = List(Real, ArbitraryInteger)
      val all = Bool :: numeric
    /** Sorts with a runtime representation */
    object runtime:
      val ints =
        List(UInt8, Int8, UInt16, Int16, UInt32, Int32, UInt64, Int64)

    val all = logical.all ++ runtime.ints


  /** A sorted (typed) variable. */
  case class Sorted(name: names.Component, sort: Sort) extends pretty.Pretty:
    def ppr = name.ppr <> pretty.colon <+> sort.ppr
    def tuple = (name, sort)
