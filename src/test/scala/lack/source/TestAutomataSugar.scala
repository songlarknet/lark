package lack.source

import lack.meta.base.Integer
import lack.meta.core
import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, UInt8}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.smt
import lack.meta.source.node.Activate

import scala.collection.mutable

/** First attempt at automaton example.
 * Manual translation from Lustre syntax to nested nodes.
 */
object TestAutomatonSugar:

  def main(args: Array[String]): Unit =
    given builder: Builder = new Builder(lack.meta.core.builder.Node.top())
    builder.invoke { new Top(_) }
    def solver() = smt.solver.gimme(verbose = false)
    smt.check.checkMany(builder.nodeRef, 4, solver)

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

    object OFF extends Initial:
      unless(btn_on) { Restart(AWAIT) }

      accel_out := accel
      light_on  := False
      speed_out := u8(0)

    object AWAIT extends State:
      unless(!btn_on) { Restart(OFF) }
      unless(cmd_set) { Restart(ON) }

      accel_out := accel
      light_on  := True
      speed_out := u8(0)

    object ON extends State:
      unless(!btn_on) { Restart(OFF) }

      accel_out := cond(when(speedo < speed_out && accel < 100) { 100 }, otherwise { accel })
      light_on  := True
      speed_out := speedo -> cond(when(cmd_set) { speedo }, otherwise { pre(speed_out) });

    // This should be auto-generated
    property("state inv") {
      OFF.active || AWAIT.active || ON.active
    }

    property("!btn_on ==> off") {
      !btn_on ==> OFF.active
    }

    property("!btn_on ==> accel_out == accel") {
      !btn_on ==> (accel_out == accel)
    }

    property("accel >= 100 => accel_out == accel") {
      (accel >= 100) ==> (accel_out == accel)
    }

    property("no set, no change") {
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

  abstract class Automaton(invocation: NodeInvocation) extends Node(invocation):
    private var stateCounter: Int = 0
    private def freshSC(): Int =
      stateCounter += 1
      stateCounter - 1

    // TODO wrap state representation in newtype
    opaque type St = UInt8
    val state = local[St]
    val reset_trigger = local[Bool]

    var initial: Option[Int] = None

    case class StateInfo(index: Int, active: Stream[Bool], reset: Stream[Bool]):
      def activate = Activate(reset = reset, when = active)

    def freshStateInfo(): StateInfo =
      val i = freshSC()
      val active = (state == u8(i))
      StateInfo(i, active, reset_trigger && active)

    case class Transition(trigger: Stream[Bool], target: Target)
    val transitions = mutable.ArrayBuffer[Transition]()
    val states = mutable.ArrayBuffer[State]()

    case class Binding(lhs: core.term.Exp, index: Int, rhs: core.term.Exp)
    val bindings = mutable.ArrayBuffer[Binding]()

    trait Target
    case class Resume(s: State) extends Target
    case class Restart(s: State) extends Target

    val outer = this

    abstract class State(val info: StateInfo = freshStateInfo()) extends Nested(info.activate):
      def active: Stream[Bool] = info.active
      states += this

      def unless(trigger: Stream[Bool])(target: Target): Unit =
        transitions += Transition(trigger, target)

      def bind[T](lhs: outer.Lhs[T], rhs: Stream[T]): Unit =
        bindings += Binding(lhs._exp, info.index, rhs._exp)

    abstract class Initial extends State():
      assert(initial.isEmpty, "cannot have more than one initial state")
      initial = Some(this.info.index)

    def finish(): Unit =
      val transitions = u8(0)
      state := u8(initial.getOrElse(0)) -> transitions

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