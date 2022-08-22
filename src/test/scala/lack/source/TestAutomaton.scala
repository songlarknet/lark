package lack.source

import lack.meta.base.Integer
import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, UInt8}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt
import lack.meta.source.node.Activate

/** First attempt at automaton example.
 * Manual translation from Lustre syntax to nested nodes.
 */
object TestAutomaton:

  def main(args: Array[String]): Unit =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    builder.invoke { new Top(_) }
    def solver() = smt.solver.gimme(verbose = true)
    smt.check.checkMany(builder.nodeRef, 4, solver)

  class Top(invocation: NodeInvocation) extends Node(invocation):
    // forall btn_on, cmd_set, ...
    val btn_on  = local[Bool]
    val cmd_set = local[Bool]
    val speedo  = local[UInt8]
    val accel   = local[UInt8]
    val cruise  = Cruise(btn_on, cmd_set, speedo, accel)


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
  class Cruise(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8], invocation: NodeInvocation) extends Node(invocation):
    // Should be able to generate a lot of this from a nicer representation
    val S_OFF     = u8(0)
    val S_AWAIT   = u8(1)
    val S_ON      = u8(2)

    val accel_out = output[UInt8]
    val light_on  = output[Bool]
    val speed_out = output[UInt8]

    val state     = local[UInt8]
    val pre_state = S_OFF -> pre(state)

    // TODO how to deal with weak/until transitions?
    state := cond(
      when(pre_state == S_OFF   && btn_on) { S_AWAIT },
      when(pre_state == S_AWAIT && !btn_on) { S_OFF },
      when(pre_state == S_AWAIT && cmd_set) { S_ON },
      when(pre_state == S_ON    && !btn_on) { S_OFF },
      otherwise { pre_state }
    )

    // Scala 3 needs reflect.Selectable to be able to refer to N_OFF.accel_out etc.
    // Activation has reset=False (transitions are all resume) and enabled when state=S_OFF
    val N_OFF = new Nested(Activate(when = state == S_OFF)) {
      val accel_out = accel
      val light_on  = False
      val speed_out = u8(0)
    }

    val N_AWAIT = new Nested(Activate(when = state == S_AWAIT)) {
      val accel_out = accel
      val light_on  = True
      val speed_out = u8(0)
    }

    val N_ON = new Nested(Activate(reset = pre_state == S_AWAIT && cmd_set, when = state == S_ON)) {
      val accel_out = local[UInt8]
      val speed_out = local[UInt8]
      val light_on  = local[Bool]

      accel_out := cond(when(speedo < speed_out && accel < 100) { 100 }, otherwise { accel })
      light_on  := True
      speed_out := speedo -> cond(when(cmd_set) { speedo }, otherwise { pre(speed_out) });
    }

    accel_out := cond(
      when(state == S_OFF)   { N_OFF.accel_out },
      when(state == S_AWAIT) { N_AWAIT.accel_out },
      when(state == S_ON)    { N_ON.accel_out },
      otherwise { accel_out } // dirty hack undefined
    )

    light_on := cond(
      when(state == S_OFF)   { N_OFF.light_on },
      when(state == S_AWAIT) { N_AWAIT.light_on },
      when(state == S_ON)    { N_ON.light_on },
      otherwise { light_on } // dirty hack undefined
    )

    speed_out := cond(
      when(state == S_OFF)   { N_OFF.speed_out },
      when(state == S_AWAIT) { N_AWAIT.speed_out },
      when(state == S_ON)    { N_ON.speed_out },
      otherwise { speed_out } // dirty hack undefined
    )

    property("state inv") {
      state == S_OFF || state == S_AWAIT || state == S_ON
    }

    property("!btn_on ==> off") {
      !btn_on ==> (state == S_OFF)
    }

    property("!btn_on ==> accel_out == accel") {
      !btn_on ==> (accel_out == accel)
    }

    property("accel >= 100 => accel_out == accel") {
      (accel >= 100) ==> (accel_out == accel)
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

  /** Hypothetical syntax sugar */
  /**
  class CruiseHyp(btn_on: Stream[Bool], cmd_set: Stream[Bool], speedo: Stream[UInt8], accel: Stream[UInt8], application: NodeApplication) extends Node(application) with Automaton:
    val accel_out = output[UInt8]
    val light_on  = output[Bool]
    val speed_out = output[UInt8]

    val OFF = new State with reflect.Selectable {
      unless(btn_on) { restart(AWAIT) }

      accel_out := accel
      light_on  := False
      speed_out := u8(0)
    }

    val AWAIT = new State with reflect.Selectable {
      unless(!btn_on) { restart(OFF) }
      unless(cmd_set) { restart(ON) }

      accel_out := accel
      light_on  := True
      speed_out := u8(0)
    }

    val ON = new State with reflect.Selectable {
      unless(!btn_on) { restart(OFF) }

      accel_out := cond(when(speedo < speed_out && accel < 100) { 100 }, otherwise { accel })
      light_on  := True
      speed_out := speedo -> cond(when(cmd_set) { speedo }, otherwise { pre(speed_out) });
    }

    property("!btn_on ==> off") {
      !btn_on ==> (state == OFF.v)
    }

    property("!btn_on ==> accel_out == accel") {
      !btn_on ==> (accel_out == accel)
    }

    property("accel >= 100 => accel_out == accel") {
      (accel >= 100) ==> (accel_out == accel)
    }
*/