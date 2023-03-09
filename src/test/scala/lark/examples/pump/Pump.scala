package lark.examples.pump

import lark.meta.base.num
import lark.meta.base.num.Integer

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Automaton
import lark.meta.source.node
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32, Real}
import lark.meta.source.prelude.Sample
import lark.meta.driver.{Prove, Compile, Grind}
import lark.meta.source.Sneaky

import scala.concurrent.duration.DurationInt

class Pump extends munit.FunSuite:
  test("Prove") {
    Prove.success(Prove.Options())
      { Pump.Top(_) }
  }

  test("Compile") {
    Compile.compile(Compile.Options(basename = "pump"))
      { Pump.Top(_) }
  }

  test("Grind") {
    Grind.grind(Grind.Options(count = 10)) { Pump.Top(_) }
  }

/** Very simple water pump controller.
 * The controller enables a water pump when the reservoir is low, and disables
 * the pump when the reservoir is high enough. This could be done with just a
 * float valve or a float switch, but we want some safety shut-offs like
 * going to an error state if the pump is continuously on for too long.
 *
 * Unfortunately, this is too small to really say anything meaningful about.
 */
object Pump:

  /** Main state machine */
  case class Pump(power: Stream[Bool], float: Stream[Bool])(invocation: Node.Invocation) extends Automaton(invocation):
    val pump_en   = output[Bool]
    val ok        = output[Bool]

    val pow_float = power && float
    val count_en  = Sample.consecutive(pump_en)

    initial(OFF)
    object OFF extends State:
      unless {
        restart(Sample.lastN(Pump.threshold, pow_float), ON)
      }

      pump_en := False
      ok      := True

    object ON extends State:
      unless {
        restart(Sample.lastN(Pump.threshold, !pow_float), OFF)
        restart(fby(u16(0), count_en) >= Pump.stuck.ticks, STUCK)
      }
      pump_en := True
      ok      := True

    object STUCK extends State:
      pump_en := False
      ok      := False

    check("not pumping for too long") {
      !Sample.lastN(Sample.Ticks(Pump.stuck.ticks + 1), pump_en)
    }

  object Pump:
    /** Consider the system to be "stuck" if the pump is on for more
     * than a minute. */
    val stuck     = Sample.Ticks(1.minute)
    val threshold = Sample.Ticks(100.millis)

  /** Top-level for verification */
  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val power     = forall[Bool]
    val float     = forall[Bool]
    subnode(Pump(power, float))
