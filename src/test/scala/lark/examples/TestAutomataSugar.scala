package lark.examples

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Automaton
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.driver.{Check, Compile, Grind}

/** Full-sugar cruise control automaton
 */
class TestAutomatonSugar extends munit.FunSuite:

  test("automaton sugar") {
    Check.success() { Top(_) }
  }

  test("automaton sugar compile") {
    Compile.compile() { new Top(_) }
  }

  test("Grind") {
    Grind.grind() { Top(_) }
  }

  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val btn_on  = forall[Bool]
    val cmd_set = forall[Bool]
    val speedo  = forall[UInt8]
    val accel   = forall[UInt8]
    val cruise  = subnode(Cruise(btn_on, cmd_set, speedo, accel))

  case class Cruise(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8])(invocation: Node.Invocation) extends Automaton(invocation):
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
