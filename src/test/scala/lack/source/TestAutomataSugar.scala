package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.automaton.Automaton
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.source.stream.{Stream, SortRepr, Bool, UInt8}
import lack.meta.driver.check

/** Full-sugar cruise control automaton
 */
class TestAutomatonSugar extends munit.FunSuite:

  test("automaton sugar") {
    check.success() { new Top(_) }
  }

  class Top(invocation: NodeInvocation) extends Node(invocation):
    // forall btn_on, cmd_set, ...
    val btn_on  = local[Bool]
    val cmd_set = local[Bool]
    val speedo  = local[UInt8]
    val accel   = local[UInt8]
    val cruise  = Cruise(btn_on, cmd_set, speedo, accel)
    cruise.finish()

  class Cruise(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8], invocation: NodeInvocation) extends Automaton(invocation):
    val accel_out = output[UInt8]
    val light_on  = output[Bool]
    val speed_out = output[UInt8]

    initial(OFF)
    object OFF extends State:
      unless {
        restart(btn_on, AWAIT)
      }
      accel_out := accel
      light_on  := False
      speed_out := u8(0)

    object AWAIT extends State:
      unless {
        restart(!btn_on, OFF)
        restart(cmd_set, ON)
      }
      accel_out := accel
      light_on  := True
      speed_out := u8(0)

    object ON extends State:
      unless {
        restart(!btn_on, OFF)
      }
      accel_out := ifthenelse(speedo < speed_out, max(accel, 100), accel)
      light_on  := True
      speed_out := speedo -> ifthenelse(cmd_set, speedo, pre(speed_out))

    check("!btn_on ==> off") {
      !btn_on ==> OFF.active
    }

    check("!btn_on ==> accel_out == accel") {
      !btn_on ==> (accel_out == accel)
    }

    check("accel >= 100 => accel_out == accel") {
      (accel >= 100) ==> (accel_out == accel)
    }

    check("no set, no change") {
      !cmd_set ==> (speed_out == u8(0) || speed_out == pre(speed_out))
    }

  object Cruise:
    def apply(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8])(using builder: Builder, location: lack.meta.macros.Location) =
      builder.invoke { invocation =>
        new Cruise(
          invocation.arg("btn_on", btn_on),
          invocation.arg("cmd_set", cmd_set),
          invocation.arg("speedo", speedo),
          invocation.arg("accel", accel),
          invocation)
      }
