package lack.meta.source

import lack.meta.macros.Location
import lack.meta.core.term.{Exp, Prim, Val}
import lack.meta.source.node.Builder
import lack.meta.source.stream.{SortRepr, Stream}
import lack.meta.base
import lack.meta.base.num.Integer
import lack.meta.core.sort.Sort

object compound:
  def pre[T: SortRepr](it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo1(it) { e => Exp.flow.Pre(it.sort, e) }

  // TODO need typed representation of Val
  def fby[T: SortRepr](v: Val, it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    require(v.check(it.sort))
    builder.memo1(it) { e => Exp.flow.Fby(it.sort, v, e) }

  // TODO may barf at runtime
  def fby[T: SortRepr](v: Stream[T], it: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    fby(v._exp.asInstanceOf[Exp.Val].v, it)

  def arrow[T: SortRepr](a: Stream[T], b: Stream[T])(using builder: Builder, location: Location): Stream[T] =
    builder.memo2(a, b) { case (e, f) => Exp.flow.Arrow(a.sort, e, f) }

  def and(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Exp.App(Sort.Bool, Prim.And, e, f)}

  def or(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Exp.App(Sort.Bool, Prim.Or, e, f)}

  def implies(x: Stream[stream.Bool], y: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo2(x, y) { case (e, f) => Exp.App(Sort.Bool, Prim.Implies, e, f)}

  def not(x: Stream[stream.Bool])(using builder: Builder, location: Location): Stream[stream.Bool] =
    builder.memo1(x) { case e => Exp.App(Sort.Bool, Prim.Not, e)}

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
    builder.memo3x1(p, t, f) { case (e, f, g) => Exp.App(t.sort, Prim.Ite, e, f, g) }

  def int[T: Num](i: Integer): Stream[T] = summon[Num[T]].const(i)

  def u8(i: Integer):  Stream[stream.UInt8]  = int[stream.UInt8](i)
  def u16(i: Integer): Stream[stream.UInt16] = int[stream.UInt16](i)
  def u32(i: Integer): Stream[stream.UInt32] = int[stream.UInt32](i)
  def u64(i: Integer): Stream[stream.UInt64] = int[stream.UInt64](i)
  def i8(i: Integer):  Stream[stream.Int8]   = int[stream.Int8](i)
  def i16(i: Integer): Stream[stream.Int16]  = int[stream.Int16](i)
  def i32(i: Integer): Stream[stream.Int32]  = int[stream.Int32](i)
  def i64(i: Integer): Stream[stream.Int64]  = int[stream.Int64](i)
  def m8(i: Integer):  Stream[stream.Mod8]   = int[stream.Mod8](i)
  def m16(i: Integer): Stream[stream.Mod16]  = int[stream.Mod16](i)
  def m32(i: Integer): Stream[stream.Mod32]  = int[stream.Mod32](i)
  def m64(i: Integer): Stream[stream.Mod64]  = int[stream.Mod64](i)

  def f32(r: Float): Stream[stream.Float32] =
    new Stream(Exp.Val(Sort.Float32, Val.Float32(r.toFloat)))

  def r32(r: Float): Stream[stream.Real32] =
    new Stream(Exp.Val(Sort.Real32, Val.Real32(r.toFloat)))

  val True: Stream[stream.Bool] = bool(true)

  val False: Stream[stream.Bool] = bool(false)

  def bool(b: Boolean): Stream[stream.Bool] =
    new Stream(Exp.Val(Sort.Bool, Val.Bool(b)))

  def tuple[A, B](a: Stream[A], b: Stream[B]): Stream[(A, B)] =
    stream.Tuple2(a, b)(using a.sortRepr, b.sortRepr)

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
      //   Prim.UnsafeCast(u)
      // def clamped[U: Num: Stream]: U =
      //   require(U.range < T.range)?
      //   Prim.UnsafeCast(clamp(U.range.min, U.range.max, u))
      // def cast[U: Num: Stream]: U =
      //   Prim.UnsafeCast(u)
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
  given Num_Mod8:   Num[stream.Mod8]   = new internal.NumImplMod(Sort.Mod8)
  given Num_Mod16:  Num[stream.Mod16]  = new internal.NumImplMod(Sort.Mod16)
  given Num_Mod32:  Num[stream.Mod32]  = new internal.NumImplMod(Sort.Mod32)
  given Num_Mod64:  Num[stream.Mod64]  = new internal.NumImplMod(Sort.Mod64)

  given Num_Float32: Num[stream.Float32] = new internal.NumImplFloat32
  given Num_Real32:  Num[stream.Real32]  = new internal.NumImplReal32

  object internal:
    abstract class NumImpl[T: SortRepr] extends Num[T] with Ord[T]:
      def add(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Exp.App(x.sort, Prim.Add, _, _) }

      def sub(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Exp.App(x.sort, Prim.Sub, _, _) }

      def mul(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Exp.App(x.sort, Prim.Mul, _, _) }

      def div(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo2(x, y) { Exp.App(x.sort, Prim.Div, _, _) }

      def negate(x: Stream[T])(using builder: Builder, location: Location): Stream[T] =
        builder.memo1(x) { Exp.App(x.sort, Prim.Negate, _) }

      def eq(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Exp.App(Sort.Bool, Prim.Eq, _, _) }

      def lt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Exp.App(Sort.Bool, Prim.Lt, _, _) }

      def le(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Exp.App(Sort.Bool, Prim.Le, _, _) }

      def gt(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Exp.App(Sort.Bool, Prim.Gt, _, _) }

      def ge(x: Stream[T], y: Stream[T])(using builder: Builder, location: Location): Stream[stream.Bool] =
        builder.memo2x1(x, y) { Exp.App(Sort.Bool, Prim.Ge, _, _) }

    class NumImplIntegral[T: SortRepr] extends NumImpl[T]:
      def const(i: Integer): Stream[T] =
        summon[SortRepr[T]].sort match
          case sort: Sort.Integral =>
            require(sort.minInclusive <= i && i <= sort.maxInclusive)
            new Stream(Exp.Val(sort, Val.Int(i)))

    class NumImplMod[T: SortRepr](mod: Sort.Mod) extends NumImpl[T]:
      def const(i: Integer): Stream[T] =
        summon[SortRepr[T]].sort match
          case sort: Sort.Mod =>
            require(sort.minInclusive <= i && i <= sort.maxInclusive)
            new Stream(Exp.Val(sort, Val.Mod(i, mod)))

    class NumImplFloat32 extends NumImpl[stream.Float32]:
      def const(i: Integer): Stream[stream.Float32] =
        new Stream(Exp.Val(Sort.Float32, Val.Float32(i.toFloat)))

    class NumImplReal32 extends NumImpl[stream.Real32]:
      def const(i: Integer): Stream[stream.Real32] =
        new Stream(Exp.Val(Sort.Real32, Val.Real32(i.toFloat)))

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
