package lark.meta.core.obc

import lark.meta.base.{names, pretty}
import lark.meta.base.names.given

import lark.meta.core.{Prop, Sort}
import lark.meta.core.term.{Exp, Flow, Val, Compound}
import lark.meta.core.term
import lark.meta.core.node.{Node, Schedule, Variable}

import lark.meta.core.obc.Obc.{Statement, Method, Class, Program, Storage}

import scala.collection.immutable.SortedMap

/** Translating from Node representation to Obc. */
object FromNode:

  object Entry:

    /** Get the bound state fields of each scheduled entry. We need to ensure
     * that all of the field names are unique, but we don't want them to be too
     * ugly. For equations we can't just use the binding name, because it might
     * occur in multiple contexts. So, we prefix each binding with the context
     * id in the format ^ctx?i.binding becomes ci_binding.
     */
    def fields(entry: Schedule.Entry, node: Node): Option[Sort.Sorted] =
      entry.binding(node) match
        case Some(Schedule.Entry.Simple(Node.Binding.Equation(lhs, eq), ctx)) => eq match
          case _ : (Flow.Pure | Flow.Arrow) =>
            None
          case _ : (Flow.Pre | Flow.Fby) =>
            Some(Sort.Sorted(makeFieldName(ctx, "c", "_", lhs), eq.sort))
        case Some(Schedule.Entry.Simple(sub: Node.Binding.Subnode, ctx)) =>
          None
        case Some(Schedule.Entry.Nested(ctx)) =>
          if ctx.requiresInitFlag
          then Some(Sort.Sorted(contextFlag(ctx), Sort.Bool))
          else None
        case None =>
          None

    def contextFlag(ctx: Node.Nested): names.Component =
      makeFieldName(ctx, "c", "init", names.Component(names.ComponentSymbol.LOCAL))

    /** Make a field name for given component inside a nested context. */
    def makeFieldName(ctx: Node.Nested, pre: String, mid: String, component: names.Component): names.Component =
      require(ctx.context.symbol == names.ComponentSymbol.STATE)
      val sym = ctx.context.ix match
        case None =>
          names.ComponentSymbol.fromScalaSymbol(mid + component.symbol.toString)
        case Some(ix) =>
          names.ComponentSymbol.fromScalaSymbol(pre + ix + mid + component.symbol.toString)
      names.Component(sym, component.ix)


    def reset(entry: Schedule.Entry, node: Node): Statement =
      entry.binding(node) match
        case Some(Schedule.Entry.Simple(Node.Binding.Equation(lhs, eq), ctx)) => eq match
          case _ : (Flow.Pure | Flow.Arrow | Flow.Pre) =>
            Statement.Skip
          case Flow.Fby(v, e) =>
            val Some(st) = fields(entry, node)
            Statement.AssignSelf(st.name, Compound.val_(v))
        case Some(Schedule.Entry.Simple(sub: Node.Binding.Subnode, ctx)) =>
          val instance = sub.subnode
          val subnode  = node.subnodes(instance)
          Statement.Call(None, klass = subnode.klass, method = Method.reset, instance = instance, args = List())
        case Some(Schedule.Entry.Nested(_)) =>
          fields(entry, node) match
            case None => Statement.Skip
            case Some(st) =>
              Statement.AssignSelf(st.name, Compound.val_(Val.Bool(true)))
        case None =>
          Statement.Skip

    def eval(entry: Schedule.Entry, node: Node): Statement =
      entry.binding(node) match
        case Some(Schedule.Entry.Simple(Node.Binding.Equation(lhs, eq), ctx)) => eq match
          case Flow.Pure(e) =>
            Statement.Assign(lhs, e)
          case Flow.Arrow(first, later) =>
            Statement.ite(
              Compound.var_(Sort.Bool, Class.self(contextFlag(ctx))),
              Statement.Assign(lhs, first),
              Statement.Assign(lhs, later))
          case _ : (Flow.Fby | Flow.Pre) =>
            val Some(st) = fields(entry, node)
            Statement.Assign(lhs, Compound.var_(st.sort, Class.self(st.name)))
        case Some(Schedule.Entry.Simple(sub: Node.Binding.Subnode, ctx)) =>
          val instance = sub.subnode
          val subnode  = node.subnodes(instance)
          val args     = sub.args
          Statement.Call(Some(instance), klass = subnode.klass, method = Method.step, instance = instance, args = args)
        case _ =>
          Statement.Skip

    def update(entry: Schedule.Entry, node: Node): Statement =
      entry.binding(node) match
        case Some(Schedule.Entry.Simple(Node.Binding.Equation(lhs, eq), ctx)) => eq match
          case _ : (Flow.Pure | Flow.Arrow) =>
            Statement.Skip
          case Flow.Fby(_, e) =>
            val Some(st) = fields(entry, node)
            Statement.AssignSelf(st.name, e)
          case Flow.Pre(e) =>
            val Some(st) = fields(entry, node)
            Statement.AssignSelf(st.name, e)
        case Some(Schedule.Entry.Simple(sub: Node.Binding.Subnode, ctx)) =>
          Statement.Skip
        case Some(Schedule.Entry.Nested(_)) =>
          fields(entry, node) match
            case None => Statement.Skip
            case Some(st) =>
              Statement.AssignSelf(st.name, Compound.val_(Val.Bool(false)))
        case None =>
          Statement.Skip

    def path(entry: Schedule.Entry, node: Node, reset: Statement, statement: Statement): Statement =
      val (ctx, ctxpath) = entry.nested(node)
      ctxpath.foldRight(statement)(path1(node, reset, _, _))

    def path1(node: Node, reset: Statement, path: Node.Path.Entry, statement: Statement): Statement =
      path match
        case m: Node.Path.Entry.Merge =>
          Statement.ite(
            m.clock,
            statement,
            Statement.Skip
          )
        case r: Node.Path.Entry.Reset =>
          Statement.ite(
            r.clock, reset, Statement.Skip
          ) <> statement

    def storage(entry: Schedule.Entry, node: Node): List[Storage] =
      entry.binding(node) match
        case Some(Schedule.Entry.Simple(sub: Node.Binding.Subnode, ctx)) =>
          val instance = sub.subnode
          val subnode  = node.subnodes(instance)
          List(Storage(instance, subnode.klass, Method.step))
        case Some(Schedule.Entry.Simple(Node.Binding.Equation(lhs, eq), ctx)) => List()
        case _ => List()

  object Methods:
    def reset(n: Node, schedule: Schedule): Method =
      val inits = for
        e <- schedule.entries
      yield Entry.reset(e, n)

      Method(Method.reset,
        List(), List(), List(), List(),
        Statement.concat(inits))

    def step(n: Node, schedule: Schedule): Method =
      def vars(mp: names.immutable.ComponentMap[Variable]) =
        mp.toList.map { case (k,v) => Sort.Sorted(k, v.sort) }

      val params  =
        n.params.map(k => Sort.Sorted(k, n.vars(k).sort)) ++
        vars(n.vars.filter(_._2.mode == Variable.Forall))
      val returns =
        vars(n.vars.filter(_._2.mode == Variable.Output))
        n.vars.filter { case (k,v) => v.mode == Variable.Output }.toList
        .map { case (k,v) => Sort.Sorted(k, v.sort)}
      val locals =
        vars(n.vars.filter(kv => kv._2.mode != Variable.Output &&
          kv._2.mode != Variable.Argument &&
          kv._2.mode != Variable.Forall))

      val evals = for
        e <- schedule.entries
        reset = Entry.reset(e, n)
        eval  = Entry.eval(e, n)
        evalX = Entry.path(e, n, reset, eval)
      yield evalX

      val updates = for
        e <- schedule.entries
        update  = Entry.update(e, n)
        updateX = Entry.path(e, n, Statement.Skip, update)
      yield updateX

      val storage = for
        e <- schedule.entries
        s <- Entry.storage(e, n)
      yield s

      val m = Method(Method.step,
        params, returns, locals, storage,
        Statement.concat(evals) <> Statement.concat(updates))

      m

  def klass(n: Node, schedule: Schedule): Class =
    val fields = for
      e <- schedule.entries
      f <- Entry.fields(e, n)
    yield f

    val objects = for
      (k, e) <- n.subnodes.toList
    yield (k -> e.klass)

    val reset = Methods.reset(n, schedule)
    val step  = Methods.step(n, schedule)

    Class(
      name    = n.klass,
      fields  = fields,
      objects = objects,
      methods = List(reset, step),
      props   = n.props
    )

  def program(nodes: Iterable[Node], schedules: names.immutable.RefMap[Schedule]): Program =
    Program(
      nodes.map { n => klass(n, schedules(n.klass)) }.toList)
