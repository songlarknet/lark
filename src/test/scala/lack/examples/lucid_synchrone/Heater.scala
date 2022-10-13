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
    Check.success() { Top(_) }
  }

  test("Compile") {
    Compile.compile(
      basename = "heater",
      output = Some(java.nio.file.Paths.get("scratch/c/")))
      { Top(_) }
  }

  test("Grind") {
    Grind.grind() { Top(_) }
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
  case class Count(d: Integer, t: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val ok = output[Bool]
    val rem = local[Base.TIME]
    val pre_rem = fby(Base.time(0), rem)

    ok  := rem == Base.time(0)
    rem := select(
      when(pre_rem == Base.time(0))
        { i32(0) },
      when(t)
        { pre_rem.as[Int32] - i32(1) },
      otherwise
        { pre_rem.as[Int32] }).as[Base.TIME]
    // It's a bit silly, but because all conditions are always evaluated, we
    // need to guard against overflow. When pre_rem == 0, pre_rem - 1 won't
    // fit in a U16.
    // Pedantically: your average Lustre compiler such as Heptagon is going to
    // compile all integers as (signed) int and silently underflow here,
    // which is undefined behaviour according to the C spec. CompCert does
    // define signed overflow though.

  /** Rising edge: true when t transitions from false to true */
  case class Edge(t: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val ok = output[Bool]
    ok := fby(False, !t) && t

  case class Heat(expected: Stream[Base.TEMP], actual: Stream[Base.TEMP])(invocation: Node.Invocation) extends Automaton(invocation):
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

  case class Command(millisecond: Stream[Bool])(invocation: Node.Invocation) extends Automaton(invocation):
    val light = output[Bool]
    val gas   = output[Bool]

    initial(OPEN)
    object OPEN extends State:
      unless {
        restart(subnode(Count(Base.delay_on, millisecond)).ok, SILENT)
      }
      light := True
      gas   := True
    object SILENT extends State:
      unless {
        restart(subnode(Count(Base.delay_off, millisecond)).ok, OPEN)
      }
      light := False
      gas   := False

  case class Light(millisecond: Stream[Bool], heatOn: Stream[Bool], lightOn: Stream[Bool])(invocation: Node.Invocation) extends Automaton(invocation):
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
        val edge = subnode(Edge(!light)).ok
        val count = subnode(Count(3, edge)).ok
        restart(fby(False, count), FAILURE)
      }
      val command = subnode(Command(millisecond))
      light := command.light
      gas   := command.gas
      nok   := False
    object FAILURE extends State:
      light := False
      gas   := False
      nok   := True

  case class Main(
    millisecond: Stream[Bool],
    restart:     Stream[Bool],
    expected:    Stream[Base.TEMP],
    actual:      Stream[Base.TEMP],
    lightOn:     Stream[Bool]
  )(invocation: Node.Invocation) extends Node(invocation):
    val light = output[Bool]
    val gas   = output[Bool]
    val ok    = output[Bool]
    val nok   = output[Bool]

    new Reset(restart):
      val heat   = subnode(Heat(expected, actual))
      val lightN = subnode(Light(millisecond, heat.on, lightOn))

      light := lightN.light
      gas   := lightN.gas
      nok   := lightN.nok
      ok    := !lightN.nok

  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val millisecond = forall[Bool]
    val restart     = forall[Bool]
    val expected    = forall[Base.TEMP]
    val actual      = forall[Base.TEMP]
    val lightOn     = forall[Bool]
    subnode(Main(millisecond, restart, expected, actual, lightOn))
