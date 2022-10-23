package lark.meta.core.node

import lark.meta.base.names.given
import lark.meta.base.collection.{MultiMapSet, Graph}
import lark.meta.base.{names, pretty}

import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow}

import scala.collection.{SortedMap, SortedSet}
import scala.math.Ordering.Implicits._

/** A schedule describes a static order to compute the parts of a node. We use
 * the schedule to compile the node to imperative code, as well as to evaluate
 * the node for testing.
 * There can be multiple valid schedules, but they should all lead to
 * equivalent results. Sometimes we can't determine a static schedule, such as
 * when the node has two mutually-dependent equations with no delay. In this
 * case we cannot compile the node.
 *
 * @param entries
 *  The scheduled order in which to compute all entries.
 */
case class Schedule(entries: List[Schedule.Entry])

object Schedule:

  /** The schedule is a list of entries. Each entry describes a piece of the
   * node that has to be computed. These pieces include the equations and
   * subnode calls from the original node, as well as some book-keeping for the
   * nested contexts that occur in merges and resets.
   * Each entry includes the path of nested contexts that the binding is nested
   * inside so that we know when to activate or reset that binding. Particular
   * variables may have more than one entry associated with them, if they have
   * multiple equations inside different branches of merges.
   */
  case class Entry(
    kind: Entry.Kind,
    path: List[names.Component],
    name: names.Component
  ) extends pretty.Pretty:
    def ppr = kind.ppr <> pretty.colon <+> names.Ref(path, name).ppr

    /** Find the binding that corresponds to this entry in the node.
     * For equation and subnode entries, returns the equation or subnode
     * binding as well as the context that encloses the binding.
     * For nested entries, returns None: not all nested contexts have bindings
     * (ie the top context), and merge bindings can have many nesteds.
     */
    def binding(node: Node): Option[(Node.Binding.Simple, Node.Nested)] =
      this.kind match
        case (Schedule.Entry.Equation | Schedule.Entry.Subnode) =>
          val (ctx, _) = nested(node)
          Some((ctx.bindings(this.name), ctx))
        case Schedule.Entry.Nested =>
          None

    def context: names.Component =
      this.path.lastOption.getOrElse(this.name)

    def nested(node: Node): (Node.Nested, Node.Path) =
      node.context(this.context)

  object Entry:
    trait Kind extends pretty.Pretty
    /** Streaming equation including pure expressions and followed-by. */
    case object Equation extends Kind:
      def ppr = "equation"
    /** Subnode invocation. */
    case object Subnode extends Kind:
      def ppr = "subnode"
    /** Book-keeping for nested contexts. */
    case object Nested extends Kind:
      def ppr = "nested"

  given Ordering_Entry: scala.math.Ordering[Entry] with
    def compare(x: Entry, y: Entry): Int =
      summon[Ordering[(String, List[names.Component], names.Component)]]
        .compare((x.kind.toString, x.path, x.name), (y.kind.toString, y.path, y.name))

  def schedule(node: Node): Schedule =
    val graph = Slurp(node, includePreDependencies = false).graph()
    try
      Schedule(graph.topsort)
    catch
      case e: lark.meta.base.collection.except.CycleException[Entry] =>
        val cyc = graph.cycles(e.value).sortBy(_.length).head
        throw new except.CyclePrettyException(node.klass, Cycle(node, graph, cyc))

  /** "Slurp" the graph vertices and edges from the program.
   *
   * @param node
   *  The node to slurp the dependencies from.
   * @param includePreDependencies
   *  If true, we include the dependencies in "pre" and "fby" expressions. When
   *  this flag is true, the graph edges reflect a "refers-to" relation, where
   *  one entry can depend on another across different time steps. When the
   *  flag is false, the graph edges reflect the "compute-before" relation,
   *  which is about dependencies in a single time step.
   *
   * XXX: the slurped graph does not contain dependencies on the parameters or
   *  "forall" variables. This is not quite right. We probably want a separate
   *  entry kind for parameter-style things that do not require any definition
   *  or scheduling.
   */
  case class Slurp(node: Node, includePreDependencies: Boolean):
    def entries(
      path: List[names.Component],
      binding: Node.Binding
    ): List[Entry] = binding match
      case b: Node.Binding.Equation =>
        List(Entry(Entry.Equation, path, b.lhs))
      case b: Node.Binding.Subnode =>
        List(Entry(Entry.Subnode, path, b.subnode))
      case b: Node.Binding.Merge =>
        b.cases.flatMap { case (k,n) =>
          entries(path, n)
        }
      case b: Node.Binding.Reset =>
        entries(path, b.nested)

    def entries(
      path: List[names.Component],
      nested: Node.Nested
    ): List[Entry] =
      val entry    = Entry(Entry.Nested, path, nested.context)
      val pathX    = path :+ nested.context
      val children = nested.children.flatMap(entries(pathX, _))
      entry :: children

    def entries(): List[Entry] =
      entries(List(), node.nested)

    /** Get entries that this variable depends on. */
    def dependencies(mpEntries: MultiMapSet[names.Component, Entry], var_ : Exp.Var): SortedSet[Entry] =
      val ref = var_.v
      ref.prefix match
        case Nil =>
          // Unqualified variables are easy, just look up the entry
          mpEntries(ref.name)
        case r :: rest =>
          // Qualified names can refer to:
          // * looking inside a subnode's results; or
          // * a nested context's internal state (for specifying invariants).
          //
          // For variables that look inside a subnode we add a dependency on
          // the subnode itself. The path inside a subnode can look further
          // inside another subnode, eg `subnode1.subnode2.result`, but in that
          // case we still just add a dependency on the outer subnode subnode1.
          //
          // Variables that look inside nested contexts let us refer to
          // internal state inside merges regardless of whether that merge is
          // active. If a merge with predicate p defines a variable x:
          // > Merge When(p) ^ctx?1:
          // >   x = fby(0, x + 1)
          // > Else When(!p) ^ctx?2:
          // >   x = -1
          // Here the plain variable `x` will only refer to the merge's value
          // when the predicate p is true, and -1 otherwise. In contrast, the
          // qualified variable `^ctx?1.x` will refer to the fby's current
          // value when p is true, and fby's held state when p is false.
          val es = mpEntries(r)
          es.toList match
            case List(Entry(Entry.Nested, path, _)) =>
              SortedSet(Entry(Entry.Equation, path ++ ref.prefix, ref.name))
            case Entry(Entry.Subnode, _, _) :: _ =>
              es
            case ess =>
              throw new except.VariableNoBindingException(node.klass, var_, ess)

    def dependencies(entries: MultiMapSet[names.Component, Entry], exp: Exp): SortedSet[Entry] =
      val vs = term.Compound.take.vars(exp)
      val ds = vs.flatMap(dependencies(entries, _))
      SortedSet.from(ds)

    def dependencies(
      entries: MultiMapSet[names.Component, Entry],
      flow: Flow
    ): SortedSet[Entry] = flow match
      case Flow.Pure(e) =>
        dependencies(entries, e)
      case Flow.Arrow(first, later) =>
        dependencies(entries, first) ++ dependencies(entries, later)
      case Flow.Pre(e) =>
        if includePreDependencies
        then dependencies(entries, e)
        else SortedSet.empty
      case Flow.Fby(_, e) =>
        if includePreDependencies
        then dependencies(entries, e)
        else SortedSet.empty

    def dependencies(
      mpEntries: MultiMapSet[names.Component, Entry],
      path: List[names.Component],
      binding: Node.Binding
    ): MultiMapSet[Entry, Entry] = binding match
      case b: Node.Binding.Equation =>
        MultiMapSet(Entry(Entry.Equation, path, b.lhs) -> dependencies(mpEntries, b.rhs))
      case b: Node.Binding.Subnode =>
        val depss = b.args.map(dependencies(mpEntries, _))
        val deps  = depss.foldLeft(SortedSet.empty)(_ ++ _)
        MultiMapSet(Entry(Entry.Subnode, path, b.subnode) -> deps)
      case b: Node.Binding.Merge =>
        // find all entries with definition in any of b.cases
        // PERF store this on node or nested
        val contexts = SortedSet(b.cases.map(_._2.context) : _*)
        val locals = mpEntries.entries.filter { case (k,vs) =>
          vs.exists(p => p.path.exists(contexts.contains(_)))
        }.keySet

        val scrutineeD = dependencies(mpEntries, b.scrutinee)
        val depss = b.cases.map { case (clock, nested) =>
          // restrict mpEntries
          val mpEntriesX = MultiMapSet(mpEntries.entries.map { case (k,vs) =>
            if locals.contains(k)
            then k -> vs.filter(v => v.path.contains(nested.context))
            else k -> vs
          })
          val (entry, deps) = dependencies(mpEntriesX, path, nested)
          MultiMapSet(entry -> scrutineeD) <> deps
        }

        MultiMapSet.concat(depss)
      case b: Node.Binding.Reset =>
        val clockD        = dependencies(mpEntries, b.clock)
        val (entry, deps) = dependencies(mpEntries, path, b.nested)
        MultiMapSet(entry -> clockD) <> deps

    def dependencies(
      mpEntries: MultiMapSet[names.Component, Entry],
      path: List[names.Component],
      nested: Node.Nested
    ): (Entry, MultiMapSet[Entry, Entry]) =
      val entry    = Entry(Entry.Nested, path, nested.context)
      val pathX    = path :+ nested.context
      val children = nested.children.map(dependencies(mpEntries, pathX, _))
      val depsX    =
        MultiMapSet.concat(children)
          .entries
          .mapValues { _ + entry }
      (entry, MultiMapSet(depsX.toSeq : _*))

    def graph(): Graph[Entry] =
      val vertices  = entries()
      val mpEntries = MultiMapSet.concat(
        vertices.map(e => MultiMapSet.just(e.name, e)))
      val (_, deps) = dependencies(mpEntries, List(), node.nested)
      Graph(vertices, deps)


  /** Information about a non-causal cycle, which is used for displaying an
   * error to the user. */
  case class Cycle(node: Node, graph: Graph[Entry], path: List[Entry]) extends pretty.Pretty:
    def ppr =
      pretty.text("The cycle is:") <@>
      pretty.indent(pprPath(path, None, None))

    /** Try to nicely print the cycle.
     * LODO: Nodes and expressions should track source locations better, print these better once that's done */
    def pprPath(
      path: List[Entry],
      lastLoc: Option[lark.meta.macros.Location],
      firstName: Option[pretty.Doc],
    ): pretty.Doc = path match
      case Nil =>
        firstName.fold(pretty.emptyDoc)(p =>
          p <> ".")
      case p :: path =>
        node.vars.get(p.name) match
          case None =>
            p.kind match
              case Entry.Nested =>
                pprPath(path, lastLoc, firstName)
              case Entry.Subnode =>
                val s = pretty.text(s"the node invocation '${p.name.symbol}'")
                s <> pretty.text(", whose arguments depend on") <@> pprPath(path, lastLoc, firstName.orElse(Some(s)))
              case Entry.Equation =>
                val s = pretty.text(s"the variable '${p.name.symbol}'")
                s <> pretty.text(", which depends on") <@> pprPath(path, lastLoc, firstName.orElse(Some(s)))
          case Some(vvar) =>
            val loc = vvar.location.copy(enclosing = None)
            if lastLoc == Some(loc)
            then pprPath(path, lastLoc, firstName)
            else if p.name.symbol.toString == ""
            then
              val s = pretty.text("the equation") <+> loc.ppr
              s <> pretty.text(", which depends on") <@> pprPath(path, Some(loc), firstName.orElse(Some(s)))
            else
              val s = pretty.text("the variable '") <> p.name.symbol.toString <> "'" <+> loc.ppr
              s <> pretty.text(", which depends on") <@> pprPath(path, Some(loc), firstName.orElse(Some(s)))

  object except:
    class ScheduleException(msg: String) extends Exception(msg)

    class VariableNoBindingException(val node: names.Ref, val e: Exp.Var, val ess: List[Entry]) extends ScheduleException(
      s"""Qualified variable '${e.pprString}' has invalid entries.
        |This should not happen in a valid program.
        | Node: ${node.pprString}
        | Sort: ${e.sort.pprString}
        | Entries: ${pretty.tupleP(ess)}
        |""".stripMargin)

    class CyclePrettyException(val node: names.Ref, val cycle: Cycle) extends ScheduleException(
      s"""Cannot schedule node '${node.pprString}' due to a cyclic dependency.
        |${cycle.pprString}""".stripMargin)
