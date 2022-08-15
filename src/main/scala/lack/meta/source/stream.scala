package lack.meta.source

import lack.meta.macros.Location
import lack.meta.core.term
import lack.meta.core.term.Exp
import lack.meta.core.sort.Sort

object stream:
  class Stream[T: SortRepr](val _exp: Exp):
    def sortRepr: SortRepr[T] = summon[SortRepr[T]]
    def sort: Sort = sortRepr.sort
    def ==(o: Stream[T])(using eq: compound.Eq[T], builder: node.Builder, location: Location): Stream[Bool] = eq.eq(this, o)
    def !=(o: Stream[T])(using eq: compound.Eq[T], builder: node.Builder, location: Location): Stream[Bool] = compound.not(eq.eq(this, o))

    // Check that all constructed streams have a sort that agrees with the type-level sort.
    // PERF: is this overkill?
    assert(_exp.sort == sort,
      s"""Stream[T] sort check: expected ${sort}, but expression has sort ${_exp.sort}.
      Expression: ${_exp.pretty}""")

  class SortRepr[T](val sort: Sort)

  // TODO: remove this, unnecessary
  object internal:
    case class Prim[T <: Sort]()

  opaque type Bool    = Sort.Bool.type
  given SortRepr_Bool: SortRepr[Bool] = new SortRepr(Sort.Bool)

  opaque type Int8    = internal.Prim[Sort.Int8.type]
  given SortRepr_Int8: SortRepr[Int8] = new SortRepr(Sort.Int8)

  opaque type UInt8   = internal.Prim[Sort.UInt8.type]
  given SortRepr_UInt8: SortRepr[UInt8] = new SortRepr(Sort.UInt8)

  opaque type Int16   = internal.Prim[Sort.Int16.type]
  given SortRepr_Int16: SortRepr[Int16] = new SortRepr(Sort.Int16)

  opaque type UInt16  = internal.Prim[Sort.UInt16.type]
  given SortRepr_UInt16: SortRepr[UInt16] = new SortRepr(Sort.UInt16)

  opaque type Int32   = internal.Prim[Sort.Int32.type]
  given SortRepr_Int32: SortRepr[Int32] = new SortRepr(Sort.Int32)

  opaque type UInt32  = internal.Prim[Sort.UInt32.type]
  given SortRepr_UInt32: SortRepr[UInt32] = new SortRepr(Sort.UInt32)

  opaque type Int64   = internal.Prim[Sort.Int64.type]
  given SortRepr_Int64: SortRepr[Int64] = new SortRepr(Sort.Int64)

  opaque type UInt64  = internal.Prim[Sort.UInt64.type]
  given SortRepr_UInt64: SortRepr[UInt64] = new SortRepr(Sort.UInt64)

  opaque type Mod8    = internal.Prim[Sort.Mod8.type]
  given SortRepr_Mod8: SortRepr[Mod8] = new SortRepr(Sort.Mod8)

  opaque type Mod16   = internal.Prim[Sort.Mod16.type]
  given SortRepr_Mod16: SortRepr[Mod16] = new SortRepr(Sort.Mod16)

  opaque type Mod32   = internal.Prim[Sort.Mod32.type]
  given SortRepr_Mod32: SortRepr[Mod32] = new SortRepr(Sort.Mod32)

  opaque type Mod64   = internal.Prim[Sort.Mod64.type]
  given SortRepr_Mod64: SortRepr[Mod64] = new SortRepr(Sort.Mod64)

  opaque type Float32 = internal.Prim[Sort.Float32.type]
  given SortRepr_Float32: SortRepr[Float32] = new SortRepr(Sort.Float32)

  opaque type Complex = internal.Prim[Sort.Complex.type]
  given SortRepr_Complex: SortRepr[Complex] = new SortRepr(Sort.Complex)

  extension (x: Stream[Complex])
    def re: Stream[Float32] = new Stream(Exp.App(Sort.Float32, term.Prim.StructGet("re", Sort.Complex), x._exp))
    def im: Stream[Float32] = new Stream(Exp.App(Sort.Float32, term.Prim.StructGet("im", Sort.Complex), x._exp))

  object Complex:
    def apply(re: Stream[Float32], im: Stream[Float32]): Stream[Complex] =
      new Stream(Exp.App(Sort.Complex, term.Prim.StructMk(Sort.Complex), re._exp, im._exp))

  // TODO more tuples
  given SortRepr_Tuple2[A: SortRepr, B: SortRepr]: SortRepr[(A, B)] =
    new SortRepr(Sort.Tuple2(summon[SortRepr[A]].sort, summon[SortRepr[B]].sort))

  extension [A: SortRepr, B: SortRepr](x: Stream[(A, B)])
    def _1: Stream[A] = new Stream(Exp.App(summon[SortRepr[A]].sort, term.Prim.StructGet("_1", Sort.Tuple2(summon[SortRepr[A]].sort, summon[SortRepr[B]].sort)), x._exp))
    def _2: Stream[B] = new Stream(Exp.App(summon[SortRepr[B]].sort, term.Prim.StructGet("_2", Sort.Tuple2(summon[SortRepr[A]].sort, summon[SortRepr[B]].sort)), x._exp))

  object Tuple2:
    def apply[A: SortRepr, B: SortRepr](_1: Stream[A], _2: Stream[B]): Stream[(A, B)] =
      val sort = Sort.Tuple2(summon[SortRepr[A]].sort, summon[SortRepr[B]].sort)
      new Stream(Exp.App(sort, term.Prim.StructMk(sort), _1._exp, _2._exp))

