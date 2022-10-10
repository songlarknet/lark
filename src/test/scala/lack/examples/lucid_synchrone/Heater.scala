package lack.examples.lucid_synchrone

import lack.meta.base.num.Integer

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Automaton
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32}
import lack.meta.driver.{Check, Compile, Grind}

/** Heater translated from Lucid-Synchrone manual:
 * https://www.di.ens.fr/~pouzet/lucid-synchrone/manual_html/manual019.html
 */
class Heater extends munit.FunSuite:

  test("Check") {
    Check.success() { new Top(_) }
  }

  test("Compile") {
    Compile.compile(
      basename = "heater",
      output = Some(java.nio.file.Paths.get("scratch/c/"))) { new Top(_) }
  }

  test("Grind") {
    Grind.grind() { new Top(_) }
  }


  object Base:
    type TEMP = UInt8
    def temp(i: Integer): Stream[TEMP] =
      u8(i)
    def low:  Integer = 4
    def high: Integer = 4

    type TIME = UInt16
    def time(i: Integer): Stream[TIME] =
      u16(i)
    def delay_on: Integer  = 500
    def delay_off: Integer = 100

  /** Count(d,t) returns true when t has been true d times. */
  class Count(d: Integer, t: Stream[Bool], invocation: Node.Invocation) extends Node(invocation):
    val ok = output[Bool]
    val rem = local[Base.TIME]
    val pre_rem = fby(Base.time(0), rem)

    ok  := rem == Base.time(0)
    rem := cond(
      when(pre_rem == Base.time(0))
        { i32(0) },
      // It's a bit silly, but because all conditions are always evaluated, we
      // need to guard against overflow. When pre_rem == 0, pre_rem - 1 won't fit in a U16.
      when(t)
        { pre_rem.as[Int32] - i32(1) },
      otherwise
        { pre_rem.as[Int32] }).as[Base.TIME]

  object Count:
    def apply(d: Integer, t: Stream[Bool])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Count(
          invocation.arg("d", d),
          invocation.arg("t", t),
          invocation)
      }.ok

  /** Rising edge: true when t transitions from false to true */
  class Edge(t: Stream[Bool], invocation: Node.Invocation) extends Node(invocation):
    val ok = output[Bool]
    ok := fby(False, !t) && t

  object Edge:
    def apply(t: Stream[Bool])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Edge(
          invocation.arg("t", t),
          invocation)
      }.ok

  class Heat(expected: Stream[Base.TEMP], actual: Stream[Base.TEMP], invocation: Node.Invocation) extends Automaton(invocation):
    val on = output[Bool]

    // Integer overflow muck
    val exp32 = expected.as[Int32]
    val lo    = exp32 - i32(Base.low)
    val hi    = exp32 + i32(Base.high)
    val act32 = actual.as[Int32]

    initial(OFF)
    object OFF extends State:
      unless {
        restart(act32 <= lo, ON)
      }
      on := False
    object ON extends State:
      unless {
        restart(act32 >= hi, OFF)
      }
      on := True

  object Heat:
    def apply(expected: Stream[UInt8], actual: Stream[UInt8])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Heat(
          invocation.arg("expected", expected),
          invocation.arg("actual", actual),
          invocation)
      }

  class Command(millisecond: Stream[Bool], invocation: Node.Invocation) extends Automaton(invocation):
    val light = output[Bool]
    val gas   = output[Bool]

    initial(OPEN)
    object OPEN extends State:
      unless {
        restart(Count(Base.delay_on, millisecond), SILENT)
      }
      light := True
      gas   := True
    object SILENT extends State:
      unless {
        restart(Count(Base.delay_off, millisecond), OPEN)
      }
      light := False
      gas   := False

  object Command:
    def apply(millisecond: Stream[Bool])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Command(
          invocation.arg("millisecond", millisecond),
          invocation)
      }

  class Light(millisecond: Stream[Bool], heatOn: Stream[Bool], lightOn: Stream[Bool], invocation: Node.Invocation) extends Automaton(invocation):
    val light = output[Bool]
    val gas   = output[Bool]
    val nok   = output[Bool]

    initial(LIGHT_OFF)
    object LIGHT_OFF extends State:
      unless {
        restart(heatOn, TRY)
      }
      light := False
      gas   := False
      nok   := False
    object LIGHT_ON extends State:
      unless {
        restart(!heatOn, LIGHT_OFF)
      }
      light := False
      gas   := True
      nok   := False
    object TRY extends State:
      unless {
        restart(lightOn, LIGHT_ON)
        restart(fby(False, Count(3, Edge(!light))), FAILURE)
      }
      val command = Command(millisecond)
      light := command.light
      gas   := command.gas
      nok   := False
    object FAILURE extends State:
      light := False
      gas   := False
      nok   := True

  object Light:
    def apply(millisecond: Stream[Bool], heatOn: Stream[Bool], lightOn: Stream[Bool])(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Light(
          invocation.arg("millisecond", millisecond),
          invocation.arg("heatOn", heatOn),
          invocation.arg("lightOn", lightOn),
          invocation)
      }

  class Main(
    millisecond: Stream[Bool],
    restart:     Stream[Bool],
    expected:    Stream[Base.TEMP],
    actual:      Stream[Base.TEMP],
    lightOn:     Stream[Bool],
    invocation: Node.Invocation
  ) extends Node(invocation):
    val light = output[Bool]
    val gas   = output[Bool]
    val ok    = output[Bool]
    val nok   = output[Bool]

    val R = new Reset(restart):
      val heat   = Heat(expected, actual)
      val lightN = Light(millisecond, heat.on, lightOn)

      light := lightN.light
      gas   := lightN.gas
      nok   := lightN.nok
      ok    := !lightN.nok


  object Main:
    def apply(
      millisecond: Stream[Bool],
      restart:     Stream[Bool],
      expected:    Stream[Base.TEMP],
      actual:      Stream[Base.TEMP],
      lightOn:     Stream[Bool],
    )(using builder: Node.Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Main(
          invocation.arg("millisecond", millisecond),
          invocation.arg("restart", restart),
          invocation.arg("expected", expected),
          invocation.arg("actual", actual),
          invocation.arg("lightOn", lightOn),
          invocation)
      }

  class Top(invocation: Node.Invocation) extends Node(invocation):
    val millisecond = forall[Bool]
    val restart     = forall[Bool]
    val expected    = forall[Base.TEMP]
    val actual      = forall[Base.TEMP]
    val lightOn     = forall[Bool]
    val main        = Main(millisecond, restart, expected, actual, lightOn)
