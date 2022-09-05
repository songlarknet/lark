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
    smt.check.checkMany(builder.nodeRef, 2, solver)

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

    // Blah: need to break cycle in state definitions, so declare the state ids first
    val S_OFF = freshStateInfo()
    val S_AWAIT = freshStateInfo()
    val S_ON = freshStateInfo()

    // XXX: why don't objects work? it seems like only the first sub-object is initialised.
    // The following doesn't throw an exception, but I expect it to:
    // object XOFF extends State(S_OFF)
    // object XAWAIT extends State(S_AWAIT):
    //   throw new Exception("never thrown")
    // object XON extends State(S_ON):
    //   throw new Exception("never thrown")

    val OFF = new Initial(S_OFF):
      unless(btn_on) { Restart(S_AWAIT) }

      accel_out := accel
      light_on  := False
      speed_out := u8(0)

    // XXX: the stream context for state transitions is wrong.
    // a transition unless(e) only activates e when current state is await,
    // but the current state depends on the transition.
    val not_btn_on = !btn_on

    val AWAIT = new State(S_AWAIT):
      unless(not_btn_on) { Restart(S_OFF) }
      unless(cmd_set) { Restart(S_ON) }

      accel_out := accel
      light_on  := True
      speed_out := u8(0)

    val ON = new State(S_ON):
      unless(not_btn_on) { Restart(S_OFF) }

      accel_out := cond(when(speedo < speed_out && accel < 100) { 100 }, otherwise { accel })
      light_on  := True
      speed_out := speedo ->
        cond(when(cmd_set) { speedo }, otherwise { pre(speed_out) });

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
      StateInfo(i, active, reset_trigger)

    case class Transition(trigger: Stream[Bool], target: Target)
    val states = mutable.Map[Int, State]()

    case class Binding(lhs: core.names.Component, lhsX: core.term.Exp, index: Int, rhs: core.term.Exp)
    val bindings = mutable.ArrayBuffer[Binding]()

    private def bindingMap: Map[core.names.Component, Map[Int, Binding]] =
      val empty = Map[core.names.Component, Map[Int, Binding]]()
      bindings.foldLeft(empty) { (mp, b) =>
        val mpi = mp.getOrElse(b.lhs, Map())
        require(!mpi.contains(b.index), s"duplicate definitions for lhs ${b.lhs} in state ${b.index}")
        mp + (b.lhs -> (mpi + (b.index -> b)))
      }

    trait Target:
      val s: StateInfo
      def isRestart: Boolean
    case class Resume(s: StateInfo) extends Target:
      val isRestart = false
    case class Restart(s: StateInfo) extends Target:
      val isRestart = true

    abstract class State(val info: StateInfo = freshStateInfo()) extends Nested(info.activate):
      val transitions = mutable.ArrayBuffer[Transition]()
      def active: Stream[Bool] =
        info.active
      states += (info.index -> this)

      def unless(trigger: Stream[Bool])(target: Target): Unit =
        transitions += Transition(trigger, target)

      def bind[T](lhs: Automaton.this.Lhs[T], rhs: Stream[T]): Unit =
        bindings += Binding(lhs.v, lhs._exp, info.index, rhs._exp)

      extension [T](lhs: Automaton.this.Lhs[T])
        protected def := (rhs: Stream[T]) =
          bind(lhs, rhs)

    abstract class Initial(info: StateInfo = freshStateInfo()) extends State(info):
      assert(initial.isEmpty, "cannot have more than one initial state")
      initial = Some(this.info.index)

    def finish(): Unit =
      require(states.size > 0, "no states. add some states to your automaton")

      val pre_state = fby(u8(initial.getOrElse(0)), state)
      def goTransitions(trs: List[Transition]): (Stream[Bool], Stream[St]) = trs match
        case Nil => (False, pre_state)
        case t :: trs =>
          val (rT,stT) = goTransitions(trs)
          val transition_reset_trigger = ifthenelse(t.trigger, bool(t.target.isRestart), rT)
          val transition_new_state = ifthenelse(t.trigger, u8(t.target.s.index), stT)
          (transition_reset_trigger, transition_new_state)

      def goStates(sts: List[State]): (Stream[Bool], Stream[St]) = sts match
        case Nil => (False, pre_state)
        case s :: sts =>
          val pre_active = pre_state == u8(s.info.index)
          val (rT,stT) = goTransitions(s.transitions.toList)
          val (rX,stX) = goStates(sts)
          val state_reset_trigger = ifthenelse(pre_active, rT, rX)
          val state_new_state = ifthenelse(pre_active, stT, stX)
          (state_reset_trigger, state_new_state)

      val (resetX, stateX) = goStates(states.values.toList)
      reset_trigger := resetX
      state := stateX

      property("GEN: finite states") {
        val assert_finite_states = u8(0) <= pre_state && pre_state < u8(stateCounter)
        assert_finite_states
      }

      bindingMap.foreach { (lhs, mpi) =>
        require(mpi.size == states.size, s"missing some bindings for states in ${lhs}, ${mpi}")
        def go(l: List[Binding]): core.term.Exp = l match
          case List(b) => b.rhs
          case b :: bs =>
            // TODO: this won't be in a-normal form
            core.term.Exp.App(b.rhs.sort, core.term.Prim.Ite, states(b.index).active._exp, b.rhs, go(bs))

        val rhs = go(mpi.values.toList)
        builder.nested.equation(lhs, rhs)
      }

/**
  * 
  Bounded model check:   Counterexample:
    { accel = 100, accel_out = 100, btn_on = true, cmd_set = true, light_on = true, reset_trigger = true, speed_out = 0, speedo = 0, state = 1 }
    { accel = 0, accel_out = 0, btn_on = false, cmd_set = true, light_on = true, reset_trigger = true, speed_out = 1, speedo = 1, state = 2 }  * 
  */