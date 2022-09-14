package lack.meta.core

import lack.meta.base.pretty
import lack.meta.base.num.{Integer, Range}

object sort:

  trait Sort extends pretty.Pretty

  object Sort:
    case object Bool extends Sort:
      def ppr = pretty.text("Bool")

    /** Fixed-width integers with integer arithmetic.
      * Arithmetic overflow is not defined. */
    class Integral(val width: Int, val signed: Boolean) extends Sort:
      def ppr = pretty.text(if (signed) "Int" else "UInt") <> pretty.value(width)
      def minInclusive: Integer = if (signed) (Integer(-1) << (width - 1)) else 0
      def maxInclusive: Integer = (if (signed) (Integer(1) << (width - 1)) else (Integer(1) << width)) - 1

    // TODO: we probably do want an arbitrary-precision Integer Sort, so we can
    // translate fixed-width integers with proof obligations.
    // This unbounded Integer sort should perhaps not be exposed in source,
    // and C compilation should die if the program uses it other than in proof obligations.

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
      def ppr = carrier.ppr <> pretty.text(s"[${minInclusive}, ${maxInclusive}]")

    /** Syntactic helper for subranges. Uses the smallest carrier set that
      * will fit the entire range, favouring unsigned integers over signed. */
    def subrange(range: Range) =
      val fits = ints.filter(i => i.minInclusive <= range.min && range.max <= i.maxInclusive)
      Subrange(range.min, range.max, fits.headOption.getOrElse(Int64))

    /** Unsigned integers with modulus arithmetic.
      * The compiled representation of these are equivalent to unsigned integers,
      * but operations have well-defined overflow semantics.
      * The SMT representation may use bitvectors.
      * TODO: rename to Bit32 or UBit32?
      */
    class Mod(val width: scala.Int) extends Sort:
      def range: Range = Range(0, (Integer(1) << width) - 1)
      def ppr = pretty.text(s"Mod$width")
      def minInclusive: Integer = range.min
      def maxInclusive: Integer = range.max

    case object Mod8  extends Mod(8)
    case object Mod16 extends Mod(16)
    case object Mod32 extends Mod(32)
    case object Mod64 extends Mod(64)

    /** IEEE754 floating-point number, single precision */
    case object Float32 extends Sort:
      def ppr = pretty.text("Float32")

    /** A mathematical real number that is represented by 32-bit floats at runtime.
     * This type is cheating a bit. */
    case object Real32 extends Sort:
      def ppr = pretty.text("Real32")

    case class Struct(name: String, fields: (String, Sort)*) extends Sort:
      require(fields.map(_._1).length == fields.map(_._1).toSet.size)
      def ppr =
        val fieldsP = fields.map(f => pretty.text(f._1) <> ":" <+> f._2.ppr)
        pretty.text(s"Struct[${name}]") <> pretty.brackets(pretty.csep(fieldsP))

    val Complex = Struct("Complex", "re" -> Float32, "im" -> Float32)

    def Tuple2(a: Sort, b: Sort) =
      Struct(s"Tuple2[${a.pprString},${b.pprString}]", "_1" -> a, "_2" -> b)
