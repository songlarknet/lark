package lack.examples

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, Int32, Real}
import lack.meta.driver.Check

/** Example of an FIR filter */
class TestFIR extends munit.FunSuite:
  test("fir filter") {
    Check.success() { new LemmaFIR(3, _) }
  }

  class LemmaFIR(n: Int, invocation: Node.Invocation) extends Node(invocation):
    val signal = local[Real]

    val lpf = FIR(List(0.5f, 0.03f, 0.02f, 0.01f), signal)
    val bounded_input =
      real(0.0) <= signal && signal <= real(100.0)
    val bounded_output =
      real(0.0) <= lpf.out && lpf.out <= real(100.0)

    sorry("assume: bounded input") {
      bounded_input
    }

    check("show: bounded output") {
      bounded_output
    }

  class FIR(coefficients: List[Float], signal: Stream[Real], invocation: Node.Invocation) extends Node(invocation):
    val out = output[Real]

    /** Single-unit delay, initialised with zero */
    def z[T: Num: SortRepr](sig: Stream[T]): Stream[T] = fby(0, sig)

    def fir(coeffs: List[Float], sig: Stream[Real]): Stream[Real] =
      coeffs match
        case List() =>
          0
        case coefficient :: rest =>
          real(coefficient) * sig + fir(rest, z(sig))

    out := fir(coefficients, signal)

  object FIR:
    def apply(coefficients: List[Float], signal: Stream[Real])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new FIR(coefficients, invocation.arg("signal", signal), invocation)
      }
