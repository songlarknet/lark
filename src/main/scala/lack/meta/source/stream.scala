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
      Expression: ${_exp.pprString}""")

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

  opaque type Real32 = internal.Prim[Sort.Real32.type]
  given SortRepr_Real32: SortRepr[Real32] = new SortRepr(Sort.Real32)
