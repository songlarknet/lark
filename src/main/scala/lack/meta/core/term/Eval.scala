package lack.meta.core.term

import lack.meta.base.names
import lack.meta.core.sort.Sort

/** Dynamic semantics of expressions and flow expressions. */
object Eval:
  type Heap = names.immutable.RefMap[Val]

  /** Evaluation options.
   *
   * @param checkRefinement
   *  If false, do not check that values of refinement types satisfy the
   *  refinement predicate.
   * @param arbitrary
   *  How to construct uninitialised values of given type.
  */
  case class Options(
    checkRefinement: Boolean = true,
    arbitrary: Sort => Val = Val.arbitrary
  )

  /** Evaluate expressions under heap */
  def exp(heap: Heap, e: Exp, options: Options): Val = e match
    case e @ Exp.Var(_, v) =>
      heap.getOrElse(v,
        throw new except.NoSuchVariableException(e, heap))
    case Exp.Val(_, v) =>
      v
    case Exp.App(_, p, args : _*) =>
      val argsV = args.map(exp(heap, _, options))
      p.eval(argsV.toList)
    case Exp.Cast(op, e) =>
      cast(op, exp(heap, e, options), options)

  /** Evaluate a cast */
  def cast(op: Exp.Cast.Op, v: Val, options: Options): Val = op match
    case Exp.Cast.Box(r) =>
      if !options.checkRefinement || r.refinesVal(v)
      then Val.Refined(r, v)
      else throw new except.RefinementException(r, v)
    case Exp.Cast.Unbox(t) => v match
      case Val.Refined(_, vX) => vX
      case _ => throw new except.CastUnboxException(op, v)

  /** Describe evaluation of flow streaming expressions as state transition */
  case class Transition(flow: Flow, options: Options):
    type State = Val

    /** Initial state */
    def init: State = flow match
      case Flow.Pure(e) =>
        Val.unit
      case Flow.Arrow(first, later) =>
        Val.Bool(false)

      case Flow.Fby(v, e) =>
        v

      case Flow.Pre(e) =>
        Val.arbitrary(flow.sort)

    /** Step from current state to new, in given heap */
    def step(state: State, heap: Heap, flow: Flow): (Val, State) = flow match
      case Flow.Pure(e) =>
        (exp(heap, e, options), Val.unit)

      case Flow.Arrow(first, later) =>
        val e =
          if state == Val.Bool(false)
          then exp(heap, first, options)
          else exp(heap, later, options)
        (e, Val.Bool(true))

      case Flow.Fby(v, e) =>
        val vX = exp(heap, e, options)
        (state, vX)

      case Flow.Pre(e) =>
        val vX = exp(heap, e, options)
        (state, vX)

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
