package lack.meta.source

import lack.meta.macros.Location
import lack.meta.core.term
import lack.meta.core.term.Exp
import lack.meta.core.Sort

class Stream[T: Stream.SortRepr](val _exp: Exp):
  def sortRepr: Stream.SortRepr[T] = summon[Stream.SortRepr[T]]
  def sort: Sort = sortRepr.sort
  def ==(o: Stream[T])(using builder: node.Builder, location: Location): Stream[Stream.Bool] =
    builder.memo2x1(this, o) { term.Flow.app(term.prim.Table.Eq, _, _) }
  def !=(o: Stream[T])(using builder: node.Builder, location: Location): Stream[Stream.Bool] = Compound.not(this == o)

  // Check that all constructed streams have a sort that agrees with the type-level sort.
  // PERF: is this overkill?
  assert(_exp.sort == sort,
    s"""Stream[T] sort check: expected ${sort}, but expression has sort ${_exp.sort}.
    Expression: ${_exp.pprString}""")

object Stream:
  class SortRepr[T](val sort: Sort)

  opaque type Bool    = Sort.Bool.type
  given SortRepr_Bool: SortRepr[Bool] = new SortRepr(Sort.Bool)

  // We don't have an instance for core.Sort.ArbitraryInteger so the user can't
  // write programs with uncompilable types. Is that too restrictive?
  opaque type Int8    = Sort.Int8.type
  given SortRepr_Int8: SortRepr[Int8] = new SortRepr(Sort.Int8)

  opaque type UInt8   = Sort.UInt8.type
  given SortRepr_UInt8: SortRepr[UInt8] = new SortRepr(Sort.UInt8)

  opaque type Int16   = Sort.Int16.type
  given SortRepr_Int16: SortRepr[Int16] = new SortRepr(Sort.Int16)

  opaque type UInt16  = Sort.UInt16.type
  given SortRepr_UInt16: SortRepr[UInt16] = new SortRepr(Sort.UInt16)

  opaque type Int32   = Sort.Int32.type
  given SortRepr_Int32: SortRepr[Int32] = new SortRepr(Sort.Int32)

  opaque type UInt32  = Sort.UInt32.type
  given SortRepr_UInt32: SortRepr[UInt32] = new SortRepr(Sort.UInt32)

  opaque type Int64   = Sort.Int64.type
  given SortRepr_Int64: SortRepr[Int64] = new SortRepr(Sort.Int64)

  opaque type UInt64  = Sort.UInt64.type
  given SortRepr_UInt64: SortRepr[UInt64] = new SortRepr(Sort.UInt64)

  opaque type Real = Sort.Real.type
  given SortRepr_Real: SortRepr[Real] = new SortRepr(Sort.Real)
