package lark.examples.brake_lights

import lark.meta.base.num

import lark.meta.source.Compound.{given, _}
import lark.meta.source.node
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{Bool, Real}

object Filter:

  case class Config(a: List[num.Real], b: List[num.Real], gain: num.Real)

  object Butterworth:
    /** High-pass filter with order 3, cutoff 1e-3 = 0.001 of sample rate.
     * Generated from http://jaggedplanet.com/iir/iir-explorer.asp with settings:
     *  High-pass, order = 3, samplerate = 88200, cutoff = 88.
     */
    def hpf_order3_cutoff1em3: Config =
      Config(
        a    = List[num.Real](-0.9875403759806987, 2.975002765896989, -2.9874621450868926, 1).reverse,
        b    = List[num.Real](-1,                  3,                 -3,                  1).reverse,
        gain = 1.0062886389669952
      )

  /** Infinite impulse response filter (IIR) */
  case class IIR(config: Config, signal: Stream[Real])(invocation: Node.Invocation) extends Node(invocation):
    val out = output[Real]
    val zero = real(0)

    /** Single-unit delay, initialised with zero:
     * > z(signal)_{i} = signal_{i - 1}
     */
    def z(sig: Stream[Real]): Stream[Real] = fby(zero, sig)

    /** Signal convolution, or a fancy dot-product:
     * > conv(coeffs, signal)_{i} = \Sum_{j = 0}^{|coeffs|} coeffs_{j} * signal_{i - j}
     */
    def conv(coeffs: List[num.Real], sig: Stream[Real]): Stream[Real] =
      coeffs match
        case List() =>
          zero
        case coefficient :: rest =>
          real(coefficient) * sig + conv(rest, z(sig))

    val gained = real(config.gain) * signal
    out := conv(config.b, gained) - conv(config.a.drop(1), z(out))

    // If the input signal is always zero, then the output should be zero:
    guarantees("always zero") {
      Sample.sofar(signal == zero) ==> (out == zero)
    }

  /** Apply an IIR filter to a signal */
  def iir(config: Config, signal: Stream[Real])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[Real] =
    node.Sugar.subnode(builder)(IIR(config, signal)).out
