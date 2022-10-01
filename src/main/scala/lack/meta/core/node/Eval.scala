package lack.meta.core.node

import lack.meta.base.names
import lack.meta.core.Sort
import lack.meta.core.term
import lack.meta.core.term.{Exp, Val, Flow}
import lack.meta.core.term.Eval.Heap

/** Dynamic semantics of streaming expressions and nodes.
 *
 * The equations in nodes can be mutually dependent, which means that
 * writing an evaluator is not totally straightforward. The rules in the
 * denotational semantics are not entirely syntax-directed and depend on
 * some outside process to choose the evaluation order.
 *
 * The semantics here makes the dependency on the outside evaluation order
 * explicit by requiring a static schedule (`node.Schedule`) for each node.
 *
 * (A lazy demand-driven evaluator would work fine too, but we need the
 * schedule for compilation anyway, so we might as well use it.)
 */
object Eval:

  case class Options(
    exp: term.Eval.Options,
    schedules: names.immutable.RefMap[Schedule]
  )



  object flow:
    /** Describe evaluation of flow streaming expressions as state transition */
    case class Transition(flow: Flow, options: term.Eval.Options):
      /** Initial state */
      def init: Transition.State = Transition.State(flow match
        case Flow.Pure(e) =>
          Val.unit
        case Flow.Arrow(first, later) =>
          Val.Bool(false)

        case Flow.Fby(v, e) =>
          v

        case Flow.Pre(e) =>
          options.arbitrary(flow.sort))

      /** The transition step is split into two stages: eval and update.
       * Eval computes the current value.
       */
      def eval(state: Transition.State, heap: Heap, flow: Flow): Val = flow match
        case Flow.Pure(e) =>
          term.Eval.exp(heap, e, options)

        case Flow.Arrow(first, later) =>
          if state.v == Val.Bool(false)
          then term.Eval.exp(heap, first, options)
          else term.Eval.exp(heap, later, options)

        case Flow.Fby(v, e) =>
          state.v

        case Flow.Pre(e) =>
          state.v

      /** The transition step is split into two stages: eval and update.
       * Update gets the next state.
       */
      def update(state: Transition.State, heap: Heap, flow: Flow): Transition.State = flow match
        case Flow.Pure(e) =>
          state

        case Flow.Arrow(first, later) =>
          Transition.State(Val.Bool(true))

        case Flow.Fby(v, e) =>
          Transition.State(term.Eval.exp(heap, e, options))

        case Flow.Pre(e) =>
          Transition.State(term.Eval.exp(heap, e, options))

    object Transition:
      case class State(v: Val)

  object except:
    class EvalException(msg: String) extends Exception(msg)

    class NoSuchVariableException(e: Exp.Var, heap: Heap) extends EvalException(
      s"""No such variable ${e.v.pprString} with sort ${e.sort.pprString}.
        |Heap: ${names.Namespace.fromMap(heap).pprString}""".stripMargin)

    class CastUnboxException(op: Exp.Cast.Op, v: Val) extends EvalException(
      s"""Cannot unbox value ${v.pprString} with op ${op}.
        |Expected a boxed value.""".stripMargin)

    class RefinementException(sort: Sort.Refinement, v: Val) extends EvalException(
      s"Cannot cast value ${v.pprString} to refinement type ${sort.pprString}.")
