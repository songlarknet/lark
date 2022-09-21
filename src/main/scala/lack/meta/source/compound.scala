package lack.meta.source

import lack.meta.macros.Location
import lack.meta.core.term.{Exp, Flow, Prim, Val}
import lack.meta.core.term.prim.Table
import lack.meta.source.node.Builder
import lack.meta.source.stream.{SortRepr, Stream}
import lack.meta.base
import lack.meta.base.num.{Integer, Real}
import lack.meta.core.sort.Sort

object compound:
  def pre[T: SortRepr](it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo1(it) { e => Flow.Pre(e) }

  // TODO need typed representation of Val
  def fby[T: SortRepr](v: Val, it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    require(v.check(it.sort))
    builder.memo1(it) { e => Flow.Fby(v, e) }

  // TODO may barf at runtime
  def fby[T: SortRepr](v: Stream[T], it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    fby(v._exp.asInstanceOf[Exp.Val].v, it)

  def arrow[T: SortRepr](a: Stream[T], b: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo2(a, b) { case (e, f) => Flow.Arrow(e, f) }

  def and(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.And, e, f) }

  def or(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.Or, e, f) }

  def implies(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Flow.app(Sort.Bool, Table.Implies, e, f) }

  def not(x: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo1(x) { case e => Flow.app(Sort.Bool, Table.Not, e) }

  extension [T: SortRepr](x: Stream[T])(using builder: Builder, location: Location)
    def ->(y: Stream[T]): Stream[T] = compound.arrow(x, y)

  extension (x: Stream[stream.Bool])(using builder: Builder, location: Location)
    def &&(y: Stream[stream.Bool]) =
      compound.and(x, y)

    def ||(y: Stream[stream.Bool]) =
      compound.or(x, y)

    def ==>(y: Stream[stream.Bool]) =
      compound.implies(x, y)

    def unary_! =
      compound.not(x)

  def ifthenelse[T: SortRepr](p: Stream[stream.Bool], t: Stream[T], f: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo3x1(p, t, f) { case (e, f, g) => Flow.app(t.sort, Table.Ite, e, f, g) }

  def int[T: Num](i: Integer): Stream[T] = summon[Num[T]].const(i)

  def u8(i: Integer):  Stream[stream.UInt8]  = int[stream.UInt8](i)
  def u16(i: Integer): Stream[stream.UInt16] = int[stream.UInt16](i)
  def u32(i: Integer): Stream[stream.UInt32] = int[stream.UInt32](i)
  def u64(i: Integer): Stream[stream.UInt64] = int[stream.UInt64](i)
  def i8(i: Integer):  Stream[stream.Int8]   = int[stream.Int8](i)
  def i16(i: Integer): Stream[stream.Int16]  = int[stream.Int16](i)
  def i32(i: Integer): Stream[stream.Int32]  = int[stream.Int32](i)
  def i64(i: Integer): Stream[stream.Int64]  = int[stream.Int64](i)

  def r32(r: Real): Stream[stream.Real32] =
    new Stream(Exp.Val(Sort.Real32, Val.Real(r)))

  def r32(r: Double): Stream[stream.Real32] =
    new Stream(Exp.Val(Sort.Real32, Val.Real(Real.decimal(r))))

  val True: Stream[stream.Bool] = bool(true)

  val False: Stream[stream.Bool] = bool(false)

  def bool(b: Boolean): Stream[stream.Bool] =
    new Stream(Exp.Val(Sort.Bool, Val.Bool(b)))

  object implicits:
    implicit def implicit_integer[T: SortRepr: Num](i: Integer): Stream[T] = summon[Num[T]].const(i)
    implicit def implicit_int[T: SortRepr: Num](i: Int): Stream[T] = summon[Num[T]].const(i)

    // this doesn't want to apply
    // implicit def tuple2[A, B](a: Stream[A], b: Stream[B]): Stream[(A, B)] =
    //   stream.Tuple2(a, b)(using a.sortRepr, b.sortRepr)


  trait Eq[T]:
    def eq(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool]

    // These operators need to live on Stream[T] itself so they can override the definitions on Object.
    // extension (x: Stream[T])(using builder: Builder)
    //   def ==(y: Stream[T]) = eq(x, y)
    //   def !=(y: Stream[T]) = !eq(x, y)

  trait Ord[T] extends Eq[T]:
    def lt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool]
    def le(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool]
    def gt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool]
    def ge(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool]

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

  given Num_Int8:   Num[stream.Int8]   = new internal.NumImplIntegral
  given Num_UInt8:  Num[stream.UInt8]  = new internal.NumImplIntegral
  given Num_Int16:  Num[stream.Int16]  = new internal.NumImplIntegral
  given Num_UInt16: Num[stream.UInt16] = new internal.NumImplIntegral
  given Num_Int32:  Num[stream.Int32]  = new internal.NumImplIntegral
  given Num_UInt32: Num[stream.UInt32] = new internal.NumImplIntegral
  given Num_Int64:  Num[stream.Int64]  = new internal.NumImplIntegral
  given Num_UInt64: Num[stream.UInt64] = new internal.NumImplIntegral

  given Num_Real32:  Num[stream.Real32]  = new internal.NumImplReal32

  object internal:
    abstract class NumImpl[T: SortRepr] extends Num[T] with Ord[T]:
      def add(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Flow.app(x.sort, Table.Add, _, _) }

      def sub(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Flow.app(x.sort, Table.Sub, _, _) }

      def mul(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Flow.app(x.sort, Table.Mul, _, _) }

      def div(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Flow.app(x.sort, Table.Div, _, _) }

      def negate(x: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo1(x) { Flow.app(x.sort, Table.Negate, _) }

      def eq(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Flow.app(Sort.Bool, Table.Eq, _, _) }

      def lt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Flow.app(Sort.Bool, Table.Lt, _, _) }

      def le(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Flow.app(Sort.Bool, Table.Le, _, _) }

      def gt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Flow.app(Sort.Bool, Table.Gt, _, _) }

      def ge(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Flow.app(Sort.Bool, Table.Ge, _, _) }

    class NumImplIntegral[T: SortRepr] extends NumImpl[T]:
      def const(i: Integer): Stream[T] =
        summon[SortRepr[T]].sort match
          case sort: Sort.Integral =>
            require(sort.minInclusive <= i && i <= sort.maxInclusive)
            new Stream(Exp.Val(sort, Val.Int(i)))

    class NumImplReal32 extends NumImpl[stream.Real32]:
      def const(i: Integer): Stream[stream.Real32] =
        new Stream(Exp.Val(Sort.Real32, Val.Real(Real(i))))

  def cond[T: SortRepr](conds: Cond.Case[T]*)(using builder: Builder, location: Location): Stream[T] =
    conds.toList match
      case Cond.Otherwise(res) :: Nil => res
      case Cond.When(p, t) :: rest => ifthenelse(p, t, cond(rest : _*))
      case _ => throw new Exception(s"cond: conditions not supported ${conds}")

  def when[T: SortRepr](pred: Stream[stream.Bool])(res: Stream[T]) =
    Cond.When(pred, res)

  def otherwise[T: SortRepr](res: Stream[T]) =
    Cond.Otherwise(res)

  object Cond:
    trait Case[T: SortRepr]
    case class When[T: SortRepr](pred: Stream[stream.Bool], res: Stream[T]) extends Case[T]
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
