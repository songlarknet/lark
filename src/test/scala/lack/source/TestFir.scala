package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32, Real32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.driver.check

/** Example of an FIR filter */
object TestFIR:

  def main(args: Array[String]): Unit =
    check.success() { new LemmaFIR(3, _) }

  class LemmaFIR(n: Int, invocation: NodeInvocation) extends Node(invocation):
    val signal = local[Real32]

    val lpf = FIR(List(0.5f, 0.03f, 0.02f, 0.01f), signal)
    val bounded_input =
      r32(0.0) <= signal && signal <= r32(100.0)
    val bounded_output =
      r32(0.0) <= lpf.out && lpf.out <= r32(100.0)

    sorry("assume: bounded input") {
      bounded_input
    }

    check("show: bounded output") {
      bounded_output
    }

  class FIR(coefficients: List[Float], signal: Stream[Real32], invocation: NodeInvocation) extends Node(invocation):
    val out = output[Real32]

    /** Single-unit delay, initialised with zero */
    def z[T: Num: SortRepr](sig: Stream[T]): Stream[T] = fby(0, sig)

    def fir(coeffs: List[Float], sig: Stream[Real32]): Stream[Real32] =
      coeffs match
        case List() =>
          0
        case coefficient :: rest =>
          r32(coefficient) * sig + fir(rest, z(sig))

    out := fir(coefficients, signal)

  object FIR:
    def apply(coefficients: List[Float], signal: Stream[Real32])(using builder: Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new FIR(coefficients, invocation.arg("signal", signal), invocation)
      }
