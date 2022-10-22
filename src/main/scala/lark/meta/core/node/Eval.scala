package lark.meta.core.node

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.assertions.impossible
import lark.meta.core.Sort
import lark.meta.core.term
import lark.meta.core.term.{Exp, Val, Flow}
import lark.meta.core.term.Eval.Heap

/** Dynamic semantics of streaming expressions and nodes.
 *
 * The equations in nodes can be mutually dependent, which means that
 * writing an evaluator is not totally straightforward. The rules in the
 * operational semantics are not entirely syntax-directed and depend on
 * some outside process to choose the evaluation order.
 *
 * The semantics here makes the dependency on the outside evaluation order
 * explicit by requiring a static schedule (`node.Schedule`) for each node.
 *
 * (A lazy demand-driven evaluator would work fine too, but we have the
 * schedule for compilation anyway, so we might as well use it here.)
 */
object Eval:
  type Heap = term.Eval.Heap
  case class State(heap: term.Eval.Heap):
    def ++(that: State): State =
      State(this.heap ++ that.heap)
    def +(kv: (names.Ref, Val)): State =
      State(this.heap + kv)
  object State:
    def empty = State(scala.collection.immutable.SortedMap.empty)

  /** Describe evaluation of a streaming program as a transition system.
   * Evaluation uses two heaps: the state heap and the value heap. The state
   * heap contains just the internal state of each operator, while the value
   * heap contains the user-specified bindings. Most terms will only refer to
   * the value heap, but sometimes invariants need to refer to the internal
   * state, so we evaluate terms with the union of both heaps.
   *
   * The transition step is split into two stages: eval and update. When a node
   * takes a step we first evaluate all of its bindings in the order specified
   * by the schedule. After all bindings have been evaluated, we go through the
   * bindings again and perform the update stage. This two-stage approach is
   * used because the updated state for a binding may refer to values that
   * occur later in the schedule than the binding itself.
   *
   * For example, given a simple counter node:
   *
   * > node counter:
   * >   pre_count = pre count;
   * >   count     = 0 -> pre_count + 1;
   *
   * The `pre_count` binding has its own internal state. We can only compute
   * the new value of the state after `count` has been computed, but we need
   * the current value of `pre_count` to compute `count`. Splitting the step
   * into two stages breaks the loop of the circular dependency.
   *
   * One standard way to encode the operational semantics of Lustre-style
   * languages is to have the step relation also return a new expression with
   * the updated state encoded in the expression. However, it's not clear to me
   * how to cleanly encode the reset contexts in such a semantics because the
   * initial state is lost after modifying the expression.
   */
  trait System:
    /** Initial state */
    def init: State
    /** The evaluate stage populates the value heap with the current value. */
    def eval(state: State, heap: Heap): Heap
    /** The update stage populates the state heap with the next state. */
    def update(state: State, heap: Heap): State

  object System:
    def empty = new System:
      def init = State(scala.collection.immutable.SortedMap.empty)
      def eval(state: State, heap: Heap): Heap = heap
      def update(state: State, heap: Heap): State = state

  extension (outer: System)
    def <>(that: System): System = new System:
      def init = outer.init ++ that.init
      def eval(state: State, heap: Heap) =
        that.eval(state, outer.eval(state, heap))
      def update(state: State, heap: Heap) =
        that.update(outer.update(state, heap), heap)


  case class Options(
    exp: term.Eval.Options,
    schedules: names.immutable.RefMap[Schedule]
  )

  def node(prefix: names.Prefix, n: Node, options: Options): System =
    val entries = options.schedules(n.name).entries.map {
      this.entry(prefix, n, _, options)
    }
    entries.foldLeft(System.empty)(_ <> _)

  def entry(prefix: names.Prefix, n: Node, entry: Schedule.Entry, options: Options): System =
    val sys = entry.binding(n) match
      case Some((flo: Node.Binding.Equation, ctx)) =>
        val st  = prefix(names.Ref(List(ctx.context), entry.name))
        val ref = prefix(names.Ref.fromComponent(entry.name))
        flow(prefix, st, ref, flo.rhs, options)
      case Some((sub: Node.Binding.Subnode, ctx)) =>
        val subnode = n.subnodes(entry.name)
        val prefixx = names.Prefix(prefix.prefix ++ List(entry.name))
        val args    = subnode.params.zip(sub.args).map { case (p, e) =>
          expbind(prefix, prefixx(p), e, options)
        }
        args.fold(System.empty)(_ <> _) <> node(prefixx, subnode, options)
      case None =>
        // Don't need to do anything for nested contexts.
        // TODO: bind INIT flag if it's useful.
        System.empty

    val (_, ctxpath) = entry.nested(n)

    ctxpath.foldRight(sys) { (entry, sys) =>
      path(prefix, entry, options, sys)
    }


  def path(prefix: names.Prefix, entry: Node.Path.Entry, options: Options, system: System): System = new System:
    def init = system.init
    def eval(state: State, heap: Heap): Heap = entry match
      case m: Node.Path.Entry.Merge =>
        if exp(prefix, state, heap, m.clock, options) == Val.Bool(true)
        then system.eval(state, heap)
        else heap
      case Node.Path.Entry.Reset(clock) =>
        if exp(prefix, state, heap, clock, options) == Val.Bool(true)
        then system.eval(state ++ init, heap)
        else system.eval(state, heap)
    def update(state: State, heap: Heap): State = entry match
      case m: Node.Path.Entry.Merge =>
        if exp(prefix, state, heap, m.clock, options) == Val.Bool(true)
        then system.update(state, heap)
        else state
      case Node.Path.Entry.Reset(clock) =>
        if exp(prefix, state, heap, clock, options) == Val.Bool(true)
        then system.update(state ++ init, heap)
        else system.update(state, heap)


  def flow(prefix: names.Prefix, st: names.Ref, ref: names.Ref, f: Flow, options: Options): System = new System:
    def init: State = f match
      case Flow.Pure(_) =>
        State.empty
      case Flow.Arrow(_, _) =>
        State.empty + (st -> Val.Bool(true))
      case Flow.Fby(v, _) =>
        State.empty + (st -> v)
      case Flow.Pre(_) =>
        State.empty + (st -> options.exp.arbitrary(f.sort))

    def eval(state: State, heap: Heap): Heap = f match
      case Flow.Pure(e) =>
        heap + (ref -> exp(prefix, state, heap, e, options))
      case Flow.Arrow(first, later) =>
        val v = state.heap(st) match
          case Val.Bool(true) => exp(prefix, state, heap, first, options)
          case Val.Bool(false) => exp(prefix, state, heap, later, options)
          case st_ =>
            impossible("state contains value of wrong type",
              "exp" -> f, "state" -> state, "st" -> st)
        heap + (ref -> v)
      case Flow.Fby(_, _) =>
        val v = state.heap(st)
        heap + (ref -> v)
      case Flow.Pre(_) =>
        val v = state.heap(st)
        heap + (ref -> v)

    def update(state: State, heap: Heap): State = f match
      case Flow.Pure(e) =>
        state
      case Flow.Arrow(first, later) =>
        state + (st -> Val.Bool(false))
      case Flow.Fby(_, e) =>
        state + (st -> exp(prefix, state, heap, e, options))
      case Flow.Pre(e) =>
        state + (st -> exp(prefix, state, heap, e, options))


  def expbind(prefix: names.Prefix, ref: names.Ref, e: Exp, options: Options): System = new System:
    def init: State = State.empty

    def eval(state: State, heap: Heap): Heap =
      val v = exp(prefix, state, heap, e, options)
      heap + (ref -> v)

    def update(state: State, heap: Heap): State = state

  def exp(prefix: names.Prefix, state: State, heap: Heap, e: Exp, options: Options): Val =
    val opt = options.exp.copy(prefix = options.exp.prefix ++ prefix)
    term.Eval.exp(state.heap ++ heap, e, opt)
