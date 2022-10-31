package lark.examples.lucid_synchrone

import lark.meta.base.num.Integer

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Automaton
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32}
import lark.meta.driver.{Prove, Compile, Grind}

/** Fast tests */
class Heater_Check extends munit.FunSuite:
  test("Prove") {
    Prove.success() { Heater.Top(_) }
  }

  test("Compile") {
    Compile.compile(Compile.Options(basename = "heater"))
      { Heater.Top(_) }
  }

/** Slow tests */
class Heater_Grind extends munit.FunSuite:
  test("Grind") {
    Grind.grind(Grind.Options(count = 10)) { Heater.Top(_) }
  }

/** Heater translated from Lucid-Synchrone manual:
 * https://www.di.ens.fr/~pouzet/lucid-synchrone/manual_html/manual019.html
 */
object Heater:


  /** Temperatures in degrees Celsius  */
  type Temp = Stream.Int16
  object Temp:
    def apply(i: Integer): Stream[Temp] =
      i16(i)

    /** Assume temperatures are between -300 and 300 degrees Celsius. */
    def min = Temp(-300)
    def max = Temp(300)
    def valid(i: Stream[Temp])(using builder: Node.Builder, location: lark.meta.macros.Location): Stream[Bool] =
      min <= i && i <= max

    /** Hysteresis for controller to reduce oscillation */
    def lowOffset  = Temp(4)
    def highOffset = Temp(4)

  object Delay:
    /** Delay between turning on gas and lighting.
     * These are Integers rather than Stream[_] because Count wants a
     * compile-time constant. We should have a Const[_] type for this.
     */
    def on: Integer  = 500
    /** Delay after an unsuccessful light attempt */
    def off: Integer = 100

  /** Count(d,t) returns true when t has been true d times. */
  case class Count(limit: Integer, t: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val limit16 = u16(limit)
    val ok      = output[Bool]
    val rem     = local[UInt16]
    val pre_rem = fby(limit16, rem)

    ok         := rem == limit16
    rem        := min(limit16, pre_rem + (ifthenelse(t, 1, 0)))

    // This intermediate invariant is required to prove that the addition above
    // does not overflow. It could reasonably be inferred by a bounds analysis.
    check("Bounds: rem") {
      rem <= limit16
    }

    // It would be nice to embed examples next to the definitions something like
    // this, and have them automatically checked:
    // examples {
    //   Count(2, Values(false, false, false)).ok ~> Values(false, false, false)
    //   Count(2, Values(true,  true,  true)).ok  ~> Values(false,  true, true)
    // }

  /** Rising edge: true when t transitions from false to true */
  case class Edge(t: Stream[Bool])(invocation: Node.Invocation) extends Node(invocation):
    val ok = output[Bool]
    ok := fby(False, !t) && t

  /** Heater bang-bang controller with hysteresis */
  case class Heat(expected: Stream[Temp], actual: Stream[Temp])(invocation: Node.Invocation) extends Automaton(invocation):
    val on = output[Bool]

    // The temperatures must be valid.
    requires("Temp bounds: expected") { Temp.valid(expected) }
    requires("Temp bounds: actual")   { Temp.valid(actual) }

    check("heating") {
      actual < expected - Temp.lowOffset implies on
    }

    initial(OFF)
    object OFF extends State:
      unless {
        restart(actual <= expected - Temp.lowOffset, ON)
      }
      on := False
    object ON extends State:
      unless {
        restart(actual >= expected + Temp.highOffset, OFF)
      }
      on := True

  case class Command(millisecond: Stream[Bool])(invocation: Node.Invocation) extends Automaton(invocation):
    val light = output[Bool]
    val gas   = output[Bool]

    initial(OPEN)
    object OPEN extends State:
      unless {
        restart(subnode(Count(Delay.on, millisecond)).ok, SILENT)
      }
      light := True
      gas   := True
    object SILENT extends State:
      unless {
        restart(subnode(Count(Delay.off, millisecond)).ok, OPEN)
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
    expected:    Stream[Temp],
    actual:      Stream[Temp],
    lightOn:     Stream[Bool]
  )(invocation: Node.Invocation) extends Node(invocation):
    requires("Temp bounds: expected") { Temp.valid(expected) }
    requires("Temp bounds: actual")   { Temp.valid(actual) }

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
    val expected    = forall[Temp]
    val actual      = forall[Temp]
    val lightOn     = forall[Bool]

    requires("Temp bounds: expected") { Temp.valid(expected) }
    requires("Temp bounds: actual")   { Temp.valid(actual) }

    subnode(Main(millisecond, restart, expected, actual, lightOn))
