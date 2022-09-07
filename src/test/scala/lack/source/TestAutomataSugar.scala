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

/** Full-sugar cruise control automaton
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

    opaque type St = UInt8
    private val MAX_STATES = 256
    private val pre_state = local[St]
    private val state = local[St]
    private val reset_trigger = local[Bool]
    private var initialState: Option[StateInfo] = None

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
      states += (info.index -> this)

      val transitions = mutable.ArrayBuffer[Transition]()
      val transitionsDelay = mutable.Queue[() => Unit]()

      def active: Stream[Bool] =
        info.active

      def unless(transitions: => Unit): Unit =
        transitionsDelay += (() => transitions)

      def restart(trigger: Stream[Bool], state: State): Unit =
        println(s"restart ${info} ${trigger} -> ${state.info}")
        transitions += Transition(trigger, Restart(state.info))

      def resume(trigger: Stream[Bool], state: State): Unit =
        transitions += Transition(trigger, Resume(state.info))

      def finish(): Unit =
        println(s"finish state ${info}")
        builder.withNesting(builder.nodeRef.nested) {
          val act = Activate(when = (pre_state == u8(info.index)), reset = fby(False, reset_trigger))
          builder.withNesting(builder.activate(act)) {
            transitionsDelay.removeAll().foreach(f => f())
          }
        }

      def bind[T](lhs: Automaton.this.Lhs[T], rhs: Stream[T]): Unit =
        bindings += Binding(lhs.v, lhs._exp, info.index, rhs._exp)

      extension [T](lhs: Automaton.this.Lhs[T])
        protected def := (rhs: Stream[T]) =
          bind(lhs, rhs)

    def initial(state: State) =
      assert(initialState.isEmpty, "cannot have more than one initial state")
      initialState = Some(state.info)

    def finish(): Unit =
      require(initialState.nonEmpty, "No initial state specified. Specify the initial state with initial(S)")
      require(states.size > 0, "no states. add some states to your automaton")

      def finishStates(): Unit =
        var i = 0
        while (i < states.size) {
          states(i).finish()
          i += 1
          require(i < MAX_STATES,
            s"state overflow: you have too many states (${states.size} >= ${MAX_STATES}).")
        }

      finishStates()

      val initialStateIndex = initialState.get.index
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
      pre_state := fby(u8(initialStateIndex), state)

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
