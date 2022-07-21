package lack.meta.core

import lack.meta.base.Integer

object sort:

  trait Sort:
    def pretty: String

  object Sort:

    case object Bool extends Sort:
      def pretty: String = "Bool"

    /** Fixed-width integers with integer arithmetic.
      * Arithmetic overflow is not defined. */
    class Integral(val width: Int, val signed: Boolean) extends Sort:
      def pretty: String = (if (signed) "Int" else "UInt") + width.toString
      def minInclusive: Integer = if (signed) (-1L << (width - 1)) else 0
      // TODO: all Longs should be BigIntegers. Long won't hold UInt64.
      def maxInclusive: Integer = if (signed) ( 1L << (width - 1)) else (1L << width)

    case object Int8   extends Integral(8, true)
    case object UInt8  extends Integral(8, false)
    case object Int16  extends Integral(16, true)
    case object UInt16 extends Integral(16, false)
    case object Int32  extends Integral(32, true)
    case object UInt32 extends Integral(32, false)
    case object Int64  extends Integral(64, true)
    case object UInt64 extends Integral(64, false)

    val ints = List(UInt8, Int8, UInt16, Int16, UInt32, Int32, UInt64, Int64)

    /** Integer interval with statically known lower and upper bounds.
      * The "carrier" or representation type dictates how values are stored.
      * Computations are performed on the carrier type.
      * Overflow */
    case class Subrange(minInclusive: Integer, maxInclusive: Integer, carrier: Integral) extends Sort:
      require(carrier.minInclusive <= minInclusive)
      require(maxInclusive <= carrier.maxInclusive)
      def pretty: String = s"${carrier.pretty}[${minInclusive}, ${maxInclusive}]"

    /** Syntactic helper for subranges. Uses the smallest carrier set that
      * will fit the entire range, favouring unsigned integers over signed. */
    def subrange(range: Range) =
      val fits = ints.filter(i => i.minInclusive <= range.min && range.max <= i.maxInclusive)
      Subrange(range.min, range.max, fits.headOption.getOrElse(Int64))

    /** Unsigned integers with modulus arithmetic.
      * The representation of these are equivalent to unsigned integers, but
      * operations have well-defined overflow semantics. */
    class Mod(val width: scala.Int) extends Sort:
      // TODO range doesn't support 32-bit unsigned or 64-bit
      def range: Range = Range(0, 1 << width)
      def pretty: String = s"Mod$width"
      def minInclusive: Integer = 0
      // TODO: all Longs should be BigIntegers. Long won't hold UInt64.
      def maxInclusive: Integer = 1L << width

    case object Mod8  extends Mod(8)
    case object Mod16 extends Mod(16)
    case object Mod32 extends Mod(32)
    case object Mod64 extends Mod(64)

    // XXX: do we want real arithmetic or IEEE754? Should they be different types?
    case object Float32 extends Sort:
      def pretty: String = "Float32"

    case class Struct(name: String, fields: (String, Sort)*) extends Sort:
      require(fields.map(_._1).length == fields.map(_._1).toSet.size)
      def pretty: String = s"Struct[${name}][${fields.mkString(", ")}]"

    val Complex = Struct("Complex", "re" -> Float32, "im" -> Float32)

    def Tuple2(a: Sort, b: Sort) =
      Struct(s"Tuple2[${a.pretty},${b.pretty}]", "_1" -> a, "_2" -> b)
