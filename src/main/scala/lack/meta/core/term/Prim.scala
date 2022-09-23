package lack.meta.core.term

import lack.meta.base.num
import lack.meta.base.num.{Integer, Real}
import lack.meta.base.{names, pretty}
import lack.meta.core.sort.Sort

/** Pure total primitives.
 * This file defines the structure of checking and evaluating primitives and
 * some helpers to define primitives, but the primitives themselves are defined
 * in lack.meta.core.term.prim.Table. */
trait Prim extends pretty.Pretty:
  /** Check the result sort of primitive when applied to arguments of given
   * sorts. Primitives can be faux-polymorphic. */
  def sort(args: List[Sort]): Sort

  /** Evaluate on given values. */
  def eval(args: List[Val]): Val

  /** Documentation - pretty-print the logical type in mock-Scala notation.
   * This is used in the error messages, but doesn't actually affect the
   * typechecking. */
  def pprType: pretty.Doc

object Prim:

  /** An error that can occur when typechecking a primitive. */
  class CheckException(prim: Prim, args: List[Sort], message: pretty.Doc) extends Exception(
    s"""Error checking primitive ${prim.pprString} : ${pretty.layout(prim.pprType)}.
       |Argument sorts: ${pretty.layout(pretty.list(args))}
       |${pretty.layout(message)}""".stripMargin)

  object CheckException:
    /** Require sorts to be exactly the same */
    def exactSame(prim: Prim, args: List[Sort]) =
      val msg =
        val dx = args.distinct
        val dlx = dx.map(Sort.logical).distinct
        if dx.length != dlx.length
        then "Sorts must be exactly the same. Maybe you're missing a cast."
        else ""
      new CheckException(prim, args, msg)


  /** An error that can occur when evaluating a primitive. */
  class EvalException(prim: Prim, args: List[Val], message: pretty.Doc) extends Exception(
    s"""Error evaluating primitive ${prim.pprString} : ${pretty.layout(prim.pprType)}.
       |Argument values: ${pretty.layout(pretty.list(args))}
       |${pretty.layout(message)}""".stripMargin)
  object EvalException:
    def impossible(prim: Prim, args: List[Val]) =
      new EvalException(prim, args,
        s"Internal failure: arguments match sorts but no rules match")

  /** Simple monomorphic primitive. */
  abstract class Simple(prim: String, val expect: List[Sort], val ret: Sort) extends Prim:
    def ppr = pretty.text(prim)
    def pprType = pretty.tupleP(expect) <+> "=>" <+> ret.ppr

    def sort(args: List[Sort]) =
      if args == expect
      then ret
      else throw new CheckException(this, args,
        "Argument sorts do not match expected sorts")

    def eval(args: List[Val]): Val =
      if args.length == expect.length && args.zip(expect).forall((a,s) => Val.check(a, s))
      then evalX(args)
      else throw new EvalException(this, args,
        "Argument values do not match expected sorts")

    def evalX(args: List[Val]): Val

  /** A primitive that takes two numbers and returns a boolean.
   * Works on integers and reals, but representation types like UInt32 must be
   * cast to integer beforehand.
   */
  abstract class Prim_nn_b extends Prim:
    def int(i: Integer, j: Integer): Boolean
    def real(i: Real, j: Real): Boolean

    def pprType = "[T: Numeric]. (T,T) => Boolean"

    def sort(args: List[Sort]) = args match
      case List(i, j)
        if i.isInstanceOf[Sort.Numeric] && i == j =>
        Sort.Bool
      case _ =>
        throw CheckException.exactSame(this, args)

    def eval(args: List[Val]) = args match
      case List(Val.Int(i), Val.Int(j)) =>
        Val.Bool(int(i, j))
      case List(Val.Real(i), Val.Real(j)) =>
        Val.Bool(real(i, j))
      case _ =>
        throw new EvalException(this, args, "")

  /** A primitive that takes two numbers and returns a number.
   * Works on integers and reals, but representation types like UInt32 must be
   * cast to integer beforehand.
   */
  abstract class Prim_nn_n extends Prim:
    def int(i: Integer, j: Integer): Integer
    def real(i: Real, j: Real): Real

    def pprType = "[T: Numeric]. (T,T) => T"

    def sort(args: List[Sort]) = args match
      case List(i, j)
        if i.isInstanceOf[Sort.Numeric] && i == j =>
        i
      case _ =>
        throw CheckException.exactSame(this, args)

    def eval(args: List[Val]) = args match
      case List(Val.Int(i), Val.Int(j)) =>
        Val.Int(int(i, j))
      case List(Val.Real(i), Val.Real(j)) =>
        Val.Real(real(i, j))
      case _ =>
        throw new EvalException(this, args, "")
