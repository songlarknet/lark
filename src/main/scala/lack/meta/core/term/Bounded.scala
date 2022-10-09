package lack.meta.core.term

import lack.meta.base.pretty

import lack.meta.core.Sort
import lack.meta.core.term

import scala.util.Try

/** Getting the runtime representation of terms, or those that can be executed
 * in bounded memory.
 *
 * This includes syntactic checking expressions to ensure that each operator,
 * variable and value has a specified precision.
 * The term "bounded" here refers to bounded-memory and bounded-precision.
 * Floating-point numbers are bounded-memory but can refer to unbounded values
 * (Inf), though we probably don't want those either in practice.
 */
object Bounded:
  /** Bounded-memory expressions.
   * These should have the invariant that repr is fixed-precision.
   */
  sealed trait BEX:
    /** The original expression */
    def original:  Exp
    /** The Exp expression with casts added everywhere */
    def annotated: Exp
    /** The bounded runtime representation / sort */
    def repr:      Sort

  object BEX:
    /** Bounded-memory variables */
    case class Var(original: Exp.Var) extends BEX:
      def repr      = original.sort
      def annotated = original
    /** Bounded-memory values */
    case class Val(original: Exp.Val, boxed: term.Val) extends BEX:
      def repr      = boxed.sort
      def annotated = Exp.Val(boxed)
    /** Cast from one bounded-memory type to another */
    case class ReboundCast(original: Exp.Cast, repr: Sort.Refinement, sub: BEX) extends BEX:
      def annotated = Exp.Cast(Exp.Cast.Box(repr),
        Exp.Cast(Exp.Cast.Unbox(repr.logical),
          sub.annotated))
    /** For a primitive that takes logically unbounded arguments, apply to bounded arguments. */
    case class ReboundApp(original: Exp.App, repr: Sort, args: List[BEX]) extends BEX:
      def annotated =
        val argsU = args.map { a =>
          a.repr match
            case s: Sort.Refinement =>
              Exp.Cast(Exp.Cast.Unbox(s.logical), a.annotated)
            case _ =>
              a.annotated
        }
        val app = Exp.App(original.sort, original.prim, argsU : _*)
        repr match
          case s: Sort.Refinement =>
            Exp.Cast(Exp.Cast.Box(s), app)
          case _ =>
            app

    /** Apply a primitive that takes bounded arguments. */
    case class App(original: Exp.App, args: List[BEX]) extends BEX:
      val repr = original.prim.sort(args.map(_.repr))
      def annotated =
        Exp.App(repr, original.prim, args.map(_.annotated) : _*)

    /** Extract either application type */
    object TakeApp:
      def unapply(bex: BEX): Option[(Prim, List[BEX])] = bex match
        case ReboundApp(e, _, args) => Some((e.prim, args))
        case App(e, args) => Some((e.prim, args))
        case _ => None


  /** Annotate an expression with fixed-precision annotations.
   * Throws Representation.except.CannotCompileException if the expression
   * requires arbitrary-precision integers.
   */
  def bound(top: Exp): BEX =
    Translate(List(
        pretty.text("While translating expression") <+> top.ppr)
    ).infer(top)

  case class Translate(where: List[pretty.Doc] = List()):
    def err(pp: pretty.Doc, exp: Exp): Nothing =
      val ctx =
        (pretty.text("In expression") <+> exp.ppr) :: where
      throw new except.CannotCompileException(
        pretty.layout(pretty.vsep(pp :: ctx)))

    def err(string: String, pp: pretty.Pretty, exp: Exp): Nothing =
      err(pretty.text("Cannot translate") <+> string <+> pretty.squote <> pp.ppr <> pretty.squote, exp)

    def requireBounded(sort: Sort, exp: Exp): Unit =
      if !isBounded(sort)
      then err("sort", sort, exp)

    def check(v: Val, s: Sort, exp: Exp): Val = (v, s) match
      case _
       if v.sort == s =>
        v
      case (v, s: Sort.Refinement)
       if v.sort == s.logical =>
        val vv = Val.Refined(s, v)
        if !Val.check(vv, s)
        then err(pretty.text("Value") <+> v.ppr <+> "does not fit in" <+> s.ppr, exp)
        vv
      case (Val.Refined(_, v), s: Sort.Refinement) =>
        check(v, s, exp)
      case _ =>
        err(pretty.text("Cannot reinterpret value") <+> v.ppr <+> "as" <+> s.ppr, exp)

    /** Check if expression can fit given bounded type, returning annotated
     * expression. */
    def check(exp: Exp, sort: Sort): BEX = exp match
      // Variables must be bounded types
      case exp: Exp.Var =>
        requireBounded(exp.sort, exp)
        BEX.Var(exp)
      // Try to cast the value
      case exp: Exp.Val =>
        val v = check(exp.v, sort, exp)
        BEX.Val(exp, v)
      case Exp.Cast(Exp.Cast.Unbox(_), sub) =>
        check(sub, sort)

      case exp@ Exp.Cast(Exp.Cast.Box(r), sub)
       if sort != r =>
        err(pretty.text("Expecting an expression of") <+> sort.ppr <+> "but encountered cast to " <+> r.ppr <> ", which requires an explicit cast", exp)
      case Exp.Cast(Exp.Cast.Box(_), v: Exp.Val) =>
        check(v, sort)
      case exp@ Exp.Cast(Exp.Cast.Box(r), sub) =>
        // Infer the representation of sub-expression and insert a cast as
        // required. We don't want to check it against the expected type 'r'
        // because it might be a different bounded type.
        val u = infer(sub)
        if u.repr == r
        then u
        else BEX.ReboundCast(exp, r, u)

      // If the application returns the exact bounded sort we want, then it's
      // fine as-is. If the return type doesn't match, then we're kind of
      // stuck. If we tried to push the desired type into the arguments, then
      // we might end up committing to a precision that doesn't work.
      // Example:
      // > \x: UInt32.
      // >   let x' = #unbox x
      // >   let a  = x' * 1024
      // >   let b  = a  / 1024
      // >   let c  = #box[UInt8] b
      // It's reasonable to check `c` and `b` as UInt8s, but we can't push
      // check `a` as a UInt8 because it won't fit.
      case exp@ Exp.App(s, prim, args : _*) =>
        if sort != s
        then err(pretty.text("Application returns") <+> s.ppr <+> "but we want a" <+> sort.ppr, exp)
        infer(exp)

    /** Infer representation mode and return annotated expression. */
    def infer(exp: Exp): BEX = exp match
      case exp: Exp.Var =>
        requireBounded(exp.sort, exp)
        BEX.Var(exp)
      case exp: Exp.Val =>
        requireBounded(exp.sort, exp)
        BEX.Val(exp, exp.v)
      case Exp.Cast(Exp.Cast.Unbox(_), sub) =>
        requireBounded(sub.sort, exp)
        check(sub, sub.sort)
      case Exp.Cast(Exp.Cast.Box(r), sub) =>
        check(exp, r)
      case exp@ Exp.App(sort, term.prim.Table.Ite, p, t, f) =>
        val pX = check(p, Sort.Bool)
        val tt = inferShallow(t)
        val ff = inferShallow(f)
        val ts = List(tt, ff).flatMap(identity).distinct.toList
        ts match
          case List() =>
            err(pretty.text("Cannot convert if-then-else as no arguments have a known representation"), exp)
          case _ :: _ :: _ =>
            err(pretty.text("Cannot convert if-then-else as arguments have different representations") <+> pretty.tupleP(ts), exp)
          case List(tt) =>
            BEX.App(exp, List(pX, check(t, tt), check(f, tt)))
      case exp@ Exp.App(sort, prim, args: _*) =>
        val reprs = args.map(inferShallow(_))
        // Assume that all logical primitives only take arguments all of same type.
        // This isn't true for if-then-else but it shouldn't take logical values.
        val ts = reprs.flatMap(identity).distinct
        ts.toList match
          case List() =>
            err(pretty.text("Cannot convert primitive") <+> prim.ppr <+> "as no arguments have a known representation", exp)
          case _ :: _ :: _ =>
            err(pretty.text("Cannot convert primitive") <+> prim.ppr <+> "as arguments have different representations" <+> pretty.tupleP(ts), exp)
          case List(t) =>
            val argsX = args.map(check(_, t))
            val repr =
              if sort == args.head.sort
              then t
              else sort
            BEX.ReboundApp(exp, repr, argsX.toList)

  /** Try to infer representation type without recursing */
  def inferShallow(exp: Exp): Option[Sort] = exp match
    case Exp.Cast(Exp.Cast.Unbox(_), sub) =>
      if isBounded(sub.sort)
      then Some(sub.sort)
      else None
    case _ =>
      if isBounded(exp.sort)
      then Some(exp.sort)
      else None

  /** Check if a sort has a runtime representation. */
  def isBounded(sort: Sort): Boolean = sort match
    case Sort.ArbitraryInteger =>
      false
    case _ =>
      true

  /** Get all subexpressions contained anywhere in the given expression,
   * including the expression itself. */
  def allSubexpressions(b: BEX): List[BEX] = b match
    case _: (BEX.Var | BEX.Val) =>
      List(b)
    case b: BEX.App =>
      b +: b.args.flatMap(allSubexpressions(_))
    case b: BEX.ReboundApp =>
      b +: b.args.flatMap(allSubexpressions(_))
    case b: BEX.ReboundCast =>
      b +: allSubexpressions(b.sub)

  object except:
    class CannotCompileException(message: String) extends Exception(message)
