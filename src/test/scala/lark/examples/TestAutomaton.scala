package lark.examples

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Node
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.driver.{Prove, Grind}

/** First attempt at automaton example.
 * Manual translation from Lustre syntax to nested nodes.
 */
class TestAutomaton extends munit.FunSuite:
  test("automaton") {
    Prove.success() { Top(_) }
  }

  test("Grind.grind") {
    Grind.grind() { Top(_) }
  }

  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val btn_on  = forall[Bool]
    val cmd_set = forall[Bool]
    val speedo  = forall[UInt8]
    val accel   = forall[UInt8]
    val cruise  = subnode(Cruise(btn_on, cmd_set, speedo, accel))


  /**
   * Very simple "cruise control" automaton in Lustre:
   *
   * node cruise(
   *   btn_on:  bool;
   *   cmd_set: bool;
   *   speedo:  int;
   *   accel:   int;
   * ) returns (
   *   accel_out: int;
   *   light_on: bool;
   *   speed_out: int;
   * )
   * let
   *   automaton
   *   initial
   *   state OFF
   *   unless
   *     if btn_on -> resume AWAIT
   *   let
   *    accel_out = accel;
   *    light_on  = false;
   *    speed_out = 0;
   *   tel
   *   state AWAIT
   *   unless
   *     if not btn_on -> resume OFF
   *     if cmd_set    -> restart ON
   *   let
   *    accel_out = accel;
   *    light_on  = true;
   *    speed_out = 0;
   *   tel
   *   state ON
   *   unless
   *     if not btn_on -> resume OFF
   *   let
   *    accel_out = if speedo < speed_out and accel < 100 then 100 else accel;
   *    light_on  = true;
   *    speed_out = speedo -> if cmd_set then speedo else pre speed_out;
   *   tel
   *
   *   --%PROPERTY not btn_on => accel_out = accel;
   *   --%PROPERTY accel >= 100 => accel_out = accel;
   * tel
  */

  /** hand-translated version */
  case class Cruise(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8])(invocation: Node.Invocation) extends Node(invocation):
    // Should be able to generate a lot of this from a nicer representation
    val S_OFF     = u8(0)
    val S_AWAIT   = u8(1)
    val S_ON      = u8(2)

    val accel_out = output[UInt8]
    val light_on  = output[Bool]
    val speed_out = output[UInt8]

    val state     = local[UInt8]
    val pre_state = S_OFF -> pre(state)

    // How to deal with weak/until transitions?
    state := select(
      when(pre_state == S_OFF   && btn_on) { S_AWAIT },
      when(pre_state == S_AWAIT && !btn_on) { S_OFF },
      when(pre_state == S_AWAIT && cmd_set) { S_ON },
      when(pre_state == S_ON    && !btn_on) { S_OFF },
      otherwise { pre_state }
    )

    val A = new Merge(state):
      val OFF = new When(S_OFF):
        accel_out := accel
        light_on  := False
        speed_out := u8(0)

      val AWAIT = new When(S_AWAIT):
        accel_out := accel
        light_on  := True
        speed_out := u8(0)

      val ON = new When(S_ON, reset = pre_state == S_AWAIT && cmd_set):
        accel_out := select(when(speedo < speed_out && accel < 100) { 100 }, otherwise { accel })
        light_on  := True
        speed_out := speedo -> select(when(cmd_set) { speedo }, otherwise { pre(speed_out) });

    check("state inv") {
      state == S_OFF || state == S_AWAIT || state == S_ON
    }

    check("!btn_on ==> off") {
      !btn_on ==> (state == S_OFF)
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
