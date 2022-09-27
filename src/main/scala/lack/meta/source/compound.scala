package lack.meta.source

import lack.meta.macros.Location
import lack.meta.core.term.{Exp, Flow, Prim, Val}
import lack.meta.core.term.prim.Table
import lack.meta.source.Node.Builder
import lack.meta.source.Stream
import lack.meta.source.Stream.SortRepr
import lack.meta.base
import lack.meta.base.num.{Integer, Real}
import lack.meta.core.Sort

object Compound:
  def pre[T: SortRepr](it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo1(it) { e => Flow.Pre(e) }

  // TODO need typed representation of Val
  def fby[T: SortRepr](v: Val, it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    require(Val.check(v, it.sort))
    builder.memo1(it) { e => Flow.Fby(v, e) }

  // TODO may barf at runtime
  def fby[T: SortRepr](v: Stream[T], it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    fby(v._exp.asInstanceOf[Exp.Val].v, it)

  def arrow[T: SortRepr](a: Stream[T], b: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo2(a, b) { case (e, f) => Flow.Arrow(e, f) }

  def and(x: Stream[Stream.Bool], y: Stream[Stream.Bool])(using builder: Builder, location: Location): Stream[Stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.And, e, f) }

  def or(x: Stream[Stream.Bool], y: Stream[Stream.Bool])(using builder: Builder, location: Location): Stream[Stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.Or, e, f) }

  def implies(x: Stream[Stream.Bool], y: Stream[Stream.Bool])(using builder: Builder, location: Location): Stream[Stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.Implies, e, f) }

  def not(x: Stream[Stream.Bool])(using builder: Builder, location: Location): Stream[Stream.Bool] =
    builder.memo1(x) { case e => Flow.app(Sort.Bool, Table.Not, e) }

  extension [T: SortRepr](x: Stream[T])(using builder: Builder, location: Location)
    def ->(y: Stream[T]): Stream[T] = Compound.arrow(x, y)

  extension (x: Stream[Stream.Bool])(using builder: Builder, location: Location)
    def &&(y: Stream[Stream.Bool]) =
      Compound.and(x, y)

    def ||(y: Stream[Stream.Bool]) =
      Compound.or(x, y)

    def ==>(y: Stream[Stream.Bool]) =
      Compound.implies(x, y)

    def unary_! =
      Compound.not(x)

  def ifthenelse[T: SortRepr](p: Stream[Stream.Bool], t: Stream[T], f: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo3x1(p, t, f) { case (e, f, g) => Flow.app(t.sort, Table.Ite, e, f, g) }

  def int[T: Num](i: Integer): Stream[T] = summon[Num[T]].const(i)

  def u8(i: Integer):  Stream[Stream.UInt8]  = int[Stream.UInt8](i)
  def u16(i: Integer): Stream[Stream.UInt16] = int[Stream.UInt16](i)
  def u32(i: Integer): Stream[Stream.UInt32] = int[Stream.UInt32](i)
  def u64(i: Integer): Stream[Stream.UInt64] = int[Stream.UInt64](i)
  def i8(i: Integer):  Stream[Stream.Int8]   = int[Stream.Int8](i)
  def i16(i: Integer): Stream[Stream.Int16]  = int[Stream.Int16](i)
  def i32(i: Integer): Stream[Stream.Int32]  = int[Stream.Int32](i)
  def i64(i: Integer): Stream[Stream.Int64]  = int[Stream.Int64](i)

  def real(r: Real): Stream[Stream.Real] =
    new Stream(Exp.Val(Sort.Real, Val.Real(r)))

  def real(r: Double): Stream[Stream.Real] =
    new Stream(Exp.Val(Sort.Real, Val.Real(Real.decimal(r))))

  val True: Stream[Stream.Bool] = bool(true)

  val False: Stream[Stream.Bool] = bool(false)

  def bool(b: Boolean): Stream[Stream.Bool] =
    new Stream(Exp.Val(Sort.Bool, Val.Bool(b)))

  object implicits:
    implicit def implicit_integer[T: SortRepr: Num](i: Integer): Stream[T] = summon[Num[T]].const(i)
    implicit def implicit_int[T: SortRepr: Num](i: Int): Stream[T] = summon[Num[T]].const(i)

  trait Eq[T]:
    def eq(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool]

  trait Ord[T] extends Eq[T]:
    def lt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool]
    def le(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool]
    def gt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool]
    def ge(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool]

    extension (x: Stream[T])(using builder: Builder, location: Location)
      def < (y: Stream[T]) = lt(x, y)
      def <=(y: Stream[T]) = le(x, y)
      def > (y: Stream[T]) = gt(x, y)
      def >=(y: Stream[T]) = ge(x, y)

  trait Num[T] extends Ord[T]:
    def add(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T]
    def sub(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T]
    def mul(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T]
    def div(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T]
    def negate(x: Stream[T])(using builder: Builder, location: Location): Stream[T]
    def const(i: Integer): Stream[T]

    // TODO: each numeric type should have a statically known range
    // def range: lack.meta.base.Range

    extension (x: Stream[T])(using builder: Builder, location: Location)
      def +(y: Stream[T]) = add(x, y)
      def -(y: Stream[T]) = sub(x, y)
      def *(y: Stream[T]) = mul(x, y)
      def /(y: Stream[T]) = div(x, y)
      def unary_- = negate(x)

      // TODO: deal with int<->real conversions
      /** Safe cast between integer types. */
      def as[U: Num: SortRepr]: Stream[U] =
        val u = summon[SortRepr[U]].sort.asInstanceOf[Sort.Refinement]
        new Stream(Exp.Cast(Exp.Cast.Box(u), Exp.Cast(Exp.Cast.Unbox(Sort.ArbitraryInteger), x._exp)))

      // Integer to integer coercions
      // Safe rounding
      // def as[U: Num: Stream]: U =
      //   builder.nodeRef.prop(...x fits in U...)
      //   Table.UnsafeCast(u)
      // def clamped[U: Num: Stream]: U =
      //   require(U.range < T.range)?
      //   Table.UnsafeCast(clamp(U.range.min, U.range.max, u))
      // def cast[U: Num: Stream]: U =
      //   Table.UnsafeCast(u)
      // Float to integer coercions
      // Integer to float coercions

  // We don't have an instance for core.Sort.ArbitraryInteger so the user can't
  // write programs with uncompilable types. Is that too restrictive?
  given Num_Int8:   Num[Stream.Int8]   = new internal.NumImplIntegral
  given Num_UInt8:  Num[Stream.UInt8]  = new internal.NumImplIntegral
  given Num_Int16:  Num[Stream.Int16]  = new internal.NumImplIntegral
  given Num_UInt16: Num[Stream.UInt16] = new internal.NumImplIntegral
  given Num_Int32:  Num[Stream.Int32]  = new internal.NumImplIntegral
  given Num_UInt32: Num[Stream.UInt32] = new internal.NumImplIntegral
  given Num_Int64:  Num[Stream.Int64]  = new internal.NumImplIntegral
  given Num_UInt64: Num[Stream.UInt64] = new internal.NumImplIntegral

  given Num_Real:  Num[Stream.Real]  = new internal.NumImplReal

  object internal:
    abstract class NumImpl[T: SortRepr] extends Num[T] with Ord[T]:
      protected def box(exp: Exp): Exp
      protected def unbox(exp: Exp): Exp
      protected def Unboxed: Sort

      protected def appBxB(prim: Prim, args: Exp*): Flow =
        Flow.Pure(box(Exp.App(Unboxed, prim, args.map(unbox) : _*)))
      protected def appBxU(ret: Sort, prim: Prim, args: Exp*): Flow =
        Flow.app(ret, prim, args.map(unbox) : _*)

      def add(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { appBxB(Table.Add, _, _) }

      def sub(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { appBxB(Table.Sub, _, _) }

      def mul(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { appBxB(Table.Mul, _, _) }

      def div(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { appBxB(Table.Div, _, _) }

      def negate(x: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo1(x) { appBxB(Table.Negate, _) }

      def eq(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool] =
        builder.memo2x1(x, y) { appBxU(Sort.Bool, Table.Eq, _, _) }

      def lt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool] =
        builder.memo2x1(x, y) { appBxU(Sort.Bool, Table.Lt, _, _) }

      def le(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool] =
        builder.memo2x1(x, y) { appBxU(Sort.Bool, Table.Le, _, _) }

      def gt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool] =
        builder.memo2x1(x, y) { appBxU(Sort.Bool, Table.Gt, _, _) }

      def ge(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[Stream.Bool] =
        builder.memo2x1(x, y) { appBxU(Sort.Bool, Table.Ge, _, _) }

    class NumImplIntegral[T: SortRepr] extends NumImpl[T]:
      protected def box(exp: Exp) =
        Exp.Cast(Exp.Cast.Box(Boxed), exp)
      protected def unbox(exp: Exp) =
        Exp.Cast(Exp.Cast.Unbox(Unboxed), exp)
      protected def Unboxed: Sort =
        Sort.ArbitraryInteger
      protected def Boxed: Sort.Refinement =
        summon[SortRepr[T]].sort
          .asInstanceOf[Sort.Refinement]

      def const(i: Integer): Stream[T] =
        summon[SortRepr[T]].sort match
          case sort: Sort.BoundedInteger =>
            require(sort.minInclusive <= i && i <= sort.maxInclusive)
            new Stream(Exp.Val(sort, Val.Refined(sort, Val.Int(i))))
          // case sort@Sort.ArbitraryInteger =>
          //   new Stream(Exp.Val(sort, Val.Int(i)))

    class NumImplReal extends NumImpl[Stream.Real]:
      protected def box(exp: Exp) =
        exp
      protected def unbox(exp: Exp) =
        exp
      protected def Unboxed: Sort =
        Sort.Real

      def const(i: Integer): Stream[Stream.Real] =
        new Stream(Exp.Val(Sort.Real, Val.Real(Real(i))))

  def cond[T: SortRepr](conds: Cond.Case[T]*)(using builder: Builder, location: Location): Stream[T] =
    conds.toList match
      case Cond.Otherwise(res) :: Nil => res
      case Cond.When(p, t) :: rest => ifthenelse(p, t, cond(rest : _*))
      case _ => throw new Exception(s"cond: conditions not supported ${conds}")

  def when[T: SortRepr](pred: Stream[Stream.Bool])(res: Stream[T]) =
    Cond.When(pred, res)

  def otherwise[T: SortRepr](res: Stream[T]) =
    Cond.Otherwise(res)

  object Cond:
    trait Case[T: SortRepr]
    case class When[T: SortRepr](pred: Stream[Stream.Bool], res: Stream[T]) extends Case[T]
    case class Otherwise[T: SortRepr](res: Stream[T]) extends Case[T]


  def abs[T: SortRepr: Num](x: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    cond(
      when(x >= int(0)) {  x },
      otherwise         { -x }
    )

  def min[T: SortRepr: Num](a: Stream[T], b: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    ifthenelse(a <= b, a, b)

  def max[T: SortRepr: Num](a: Stream[T], b: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    ifthenelse(a >= b, a, b)
