package lark.meta.source.prelude

import lark.meta.base.num

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.node
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{Bool, SortRepr, UInt16, Real}

object Sample:

  /** Sample-and-hold */
  // BADSOURCE: source language freshening is bogus, need to pass SortRepr[T] as explicit `using val` argument
  case class Hold[T](clock: Stream[Bool], value: Stream[T], default: Stream[T])(invocation: Node.Invocation)(using val repr: SortRepr[T]) extends Node(invocation):
    val out = output[T]
    // BADSOURCE: `fby(default, out)` doesn't work here because `default` is not a value.
    // the subnode invocation below gives it a fresh parameter name.
    // should have a separate type Const[T]
    out := ifthenelse(clock, value, default -> pre(out))

  /** A "sample and hold" that latches the current value whenever the clock is true */
  def hold[T: SortRepr](clock: Stream[Bool], value: Stream[T], default: Stream[T])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[T] =
    node.Sugar.subnode(builder)(Hold(clock, value, default)).out

  /** Time duration in discrete steps */
  case class Ticks(ticks: num.Integer)
  object Ticks:
    val SAMPLE_RATE: num.Integer = 100
    val SAMPLE_PERIOD_MS: num.Integer = 1000 / SAMPLE_RATE

    def apply(duration: scala.concurrent.duration.FiniteDuration): Ticks =
      Ticks(duration.toMillis / SAMPLE_PERIOD_MS)


  /** True if the stream e has been true for n or more ticks. */
  // TODO: want 'Const[T]' for ticks
  case class LastN(n: Stream[UInt16], e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val count     = output[UInt16]
    val out       = output[Bool]
    val pre_count = fby(u16(0), count)

    count := select(
      when(e && pre_count <  LastN.MAX) { pre_count + 1 },
      when(e && pre_count >= LastN.MAX) { LastN.MAX },
      otherwise                         { 0 }
    )

    out   := count >= n
  object LastN:
    val MAX = 65534

  /** True if the stream e has been true for n or more ticks. */
  def lastN(n: Ticks, e: Stream[Bool])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[Bool] =
    require(n.ticks <= LastN.MAX)
    node.Sugar.subnode(builder)(LastN(u16(n.ticks), e)).out

  /** Count how many ticks the stream has been consecutively true */
  def consecutive(e: Stream[Bool])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[UInt16] =
    node.Sugar.subnode(builder)(LastN(u16(0), e)).count


  /** The stream has always been true "so far".
   * We sometimes call this "always" but in strict temporal logic "always"
   * would also refer to the future.
   */
  case class SoFar(e: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val out  = output[Bool]
    out     := e && fby(True, out)

  /** The stream has always been true "so far". */
  def sofar(e: Stream[Bool])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[Bool] =
    node.Sugar.subnode(builder)(SoFar(e)).out

  /** Toggle between on and off every n ticks. Initially false. */
  case class Toggle(n: Ticks)(invocation: Node.Invocation) extends Node(invocation):
    val out   = output[Bool]
    val count = local[UInt16]
    count   := fby(u16(0),
      ifthenelse(count >= n.ticks, u16(0), count + u16(1)))
    out     := fby(False,
      ifthenelse(count == n.ticks, !out, out))

  /** Toggle between on and off every n ticks. Initially false. */
  def toggle(n: Ticks)(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[Bool] =
    node.Sugar.subnode(builder)(Toggle(n)).out
