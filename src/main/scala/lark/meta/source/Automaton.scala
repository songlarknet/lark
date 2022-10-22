package lark.meta.source

import lark.meta.base.names
import lark.meta.core
import lark.meta.source.Compound.{given, _}
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.Node

import scala.collection.mutable

/** Syntactic sugar for describing automata.
 *
 * The automata are loosely inspired by the paper "A conservative extension
 * of synchronous data-flow with state machines" (Colaço 2005), but I haven't
 * implemented the "last" operator or weak "until" transitions yet.
 * Parameterised state machines would be quite useful too ("Mixing signals
 * and modes in synchronous data-flow systems", Colaço 2006) and seem doable.
 *
 * I'm not convinced that the semantics in either of these papers are totally
 * correct though - weak "until" resets seem to only reset the strong
 * transition (the "unless" part), rather than the main part of the state.
 *
 * The user is expected to create a node that inherits from this class and
 * define named local state objects that inherit from Automaton.State. Each
 * state object defines its transitions and bindings. The user must specify
 * the initial state by calling initial(state) from their automaton's
 * constructor.
 *
 * Too much magic?
 *
 * OPTIMISE: looking at the core program, the main difference between my
 * hand-written automaton and the generated one is that this generated one
 * has lots of resets. each state has two reset contexts, one for resetting
 * the transitions, and one for resetting the state bindings. we should be
 * able to figure out ahead-of-time which states are actually restarted, and
 * only introduce reset contexts for those.
 * The automata translations described in "a conservative extension"
 * (Colaço 2005) and "hierarchical state machines as modular horn clauses"
 * (Garoche 2016) don't make it statically clear which states can reset and
 * which cannot, either. I wonder whether this was one of the issues that
 * made Kind2's automata a bit slow, if reset contexts introduce extra copies
 * of the state there too.
 */
abstract class Automaton(invocation: node.Invocation) extends Node(invocation):
  /** The user must specify their initial state */
  def initial(state: State) =
    assert(initialState.isEmpty, s"Cannot set initial state multiple times. Have value ${initialState}, tried to set to ${state.info}")
    initialState = Some(state.info)

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

  case class StateInfo(st: Stream[St], indexInt: Int, active: Stream[Bool], reset: Stream[Bool])

  private def freshStateInfo(): StateInfo =
    val i = freshSC()

    // TODO: thread through nice name
    val st = u8(i)
    val active = (state == st)
    StateInfo(st, i, active, reset_trigger)

  case class Transition(trigger: Stream[Bool], target: Target)
  val states = mutable.Map[Int, State]()

  val mergeTransition = new Merge(pre_state) {}
  val mergeStates = new Merge(state) {}

  trait Target:
    val s: StateInfo
    def isRestart: Boolean
  case class Resume(s: StateInfo) extends Target:
    val isRestart = false
  case class Restart(s: StateInfo) extends Target:
    val isRestart = true

  abstract class State(val info: StateInfo = freshStateInfo()) extends mergeStates.When(target = info.st, reset = info.reset):
    states += (info.indexInt -> this)

    val transitions = mutable.ArrayBuffer[Transition]()
    val transitionsDelay = mutable.Queue[() => Unit]()

    def active: Stream[Bool] =
      info.active

    def unless(transitions: => Unit): Unit =
      transitionsDelay += (() => transitions)

    /** HACK: only call this from inside an unless block.
     * The transitions need to execute in a different context from the main
     * definitions, as the strong transition may jump to a different state.
     * Given:
     * > object STAY_ONE_TICK extends State:
     * >  unless {
     * >    restart(False --> True, DONE)
     * >  }
     * >  here := False --> True
     * The two occurrences of "False --> True" have different clocks...
     */
    def restart(trigger: Stream[Bool], state: State): Unit =
      transitions += Transition(trigger, Restart(state.info))

    /** HACK: only call this from inside an unless block. */
    def resume(trigger: Stream[Bool], state: State): Unit =
      transitions += Transition(trigger, Resume(state.info))

    private def goTransitions(trs: List[Transition]): (Stream[Bool], Stream[St]) = trs match
      case Nil => (False, pre_state)
      case t :: trs =>
        val (rT,stT) = goTransitions(trs)
        val transition_reset_trigger = ifthenelse(t.trigger, bool(t.target.isRestart), rT)
        val transition_new_state = ifthenelse(t.trigger, t.target.s.st, stT)
        (transition_reset_trigger, transition_new_state)

    /** Should only be called by Automaton.finish */
    private[source]
    def finish(): Unit =
      builder.withNesting(Automaton.this.builder.nested) {
        val when  = (pre_state == info.st)
        val reset = fby(False, reset_trigger)
        val nest  = mergeTransition.merge
          .when(when._exp)
          .reset(reset._exp)
        builder.withNesting(nest) {
          transitionsDelay.removeAll().foreach(f => f())
          val (resetX,stateX) = goTransitions(transitions.toList)
          reset_trigger := resetX
          state := stateX
        }
      }

  private def finishAutomaton(): Unit =
    require(states.size > 0, "no states. add some states to your automaton")
    require(initialState.nonEmpty, "No initial state specified. Specify the initial state with initial(S)")

    // Loop through all of the states, "finishing" them.
    // This forces each state to register its transitions.
    // The states might be declared as local objects, which are lazily
    // initialised, so one state registering its transitions might initialise
    // the target state objects. So we loop through the states array such
    // that we'll still find any values that were added by previous calls
    // to finish.
    def finishStates(): Unit =
      var i = 0
      while (i < states.size) {
        states(i).finish()
        i += 1
        require(i < MAX_STATES,
          s"state overflow: you have too many states (${states.size} >= ${MAX_STATES}).")
      }

    finishStates()

    val initialStateSt = initialState.get.indexInt
    pre_state := fby(u8(initialStateSt), state)

    base.bindProperty(core.Prop.Syntax.Generated.check, "finite states") {
      val assert_finite_states = u8(0) <= pre_state && pre_state < u8(stateCounter)
      assert_finite_states
    }

  base.afterConstructor { () =>
    finishAutomaton()
  }
