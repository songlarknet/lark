package lack.meta.core.node

import lack.meta.base.names.given
import lack.meta.base.{names, pretty}

import lack.meta.core.term
import lack.meta.core.term.{Exp, Flow}

import scala.collection.{SortedMap, SortedSet}
import scala.math.Ordering.Implicits._

/** A schedule describes a static order to compute the parts of a node. We use
 * the schedule to compile the node to imperative code, as well as to evaluate
 * the node for testing.
 * There can be multiple valid schedules, but they should all lead to
 * equivalent results. Sometimes we can't determine a static schedule, such as
 * when the node has two mutually-dependent equations with no delay. In this
 * case we cannot compile the node.
 */
case class Schedule(list: Schedule.Entry)

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

  case class Graph(
    vertices: SortedSet[Entry],
    edges: MultiMap[Entry, Entry]
  ):
    def scheduleWithNode(node: Node): List[Entry] =
      try
        topsorts(SortedSet.empty, SortedSet.empty, vertices.toList)._1
      catch
        case e: except.CycleEntryException =>
          val cyc = cycles(e.entry).sortBy(_.length).head
          throw new except.CyclePrettyException(node.path, Graph.Cycle(node, this, cyc))

    def cycles(to: Entry): List[List[Entry]] =
      edges(to).toList.flatMap(cycles(SortedSet(to), _))

    def cycles(seen: SortedSet[Entry], from: Entry): List[List[Entry]] =
      if seen.contains(from)
      then List(List(from))
      else for
        fromX <- edges(from).toList
        fromXX <- cycles(seen + from, fromX)
      yield fromX :: fromXX

    def topsorts(
      emitted: SortedSet[Entry],
      successors: SortedSet[Entry],
      entries: List[Entry]
    ): (List[Entry], SortedSet[Entry]) = entries match
      case Nil => (List(), emitted)
      case e :: es =>
        val (l1, e1) = topsort(emitted, successors, e)
        val (l2, e2) = topsorts(e1, successors, es)
        (l1 ++ l2, e2)

    def topsort(
      emitted: SortedSet[Entry],
      successors: SortedSet[Entry],
      entry: Entry
    ): (List[Entry], SortedSet[Entry]) =
      if successors.contains(entry) then
        throw new except.CycleEntryException(entry)
      else if emitted.contains(entry) then
        (List(), emitted)
      else
        val (l1, e1) = topsorts(emitted + entry, successors + entry, edges(entry).toList)
        (entry :: l1, e1)

  object Graph:
    case class Cycle(node: Node, graph: Graph, path: List[Entry]) extends pretty.Pretty:
      def ppr =
        pretty.text("The cycle is:") <@>
        pretty.indent(pprPath(path, None, None))

      /** Try to nicely print the cycle.
       * TODO: Nodes and expressions should track source locations better, print these better once that's done */
      def pprPath(
        path: List[Entry],
        lastLoc: Option[lack.meta.macros.Location],
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

  case class MultiMap[K: scala.math.Ordering, V: scala.math.Ordering](entries: SortedMap[K, SortedSet[V]]):
    def <>(that: MultiMap[K, V]): MultiMap[K, V] =
      MultiMap(
        that.entries.foldLeft(this.entries) { case (acc, (k,v)) =>
          acc + (k -> (acc.getOrElse(k, SortedSet.empty[V]) ++ v))
        })

    def apply(key: K): SortedSet[V] =
      entries.getOrElse(key, SortedSet.empty)

  object MultiMap:
    def apply[K: scala.math.Ordering, V: scala.math.Ordering](elems: (K, SortedSet[V])*): MultiMap[K, V] =
      MultiMap[K, V](SortedMap(elems : _*))

    def empty[K: scala.math.Ordering, V: scala.math.Ordering] =
      MultiMap[K, V](SortedMap.empty[K, SortedSet[V]])

    def just[K: scala.math.Ordering, V: scala.math.Ordering](key: K, value: V) =
      MultiMap(SortedMap(key -> SortedSet(value)))

    def concat[K: scala.math.Ordering, V: scala.math.Ordering](maps: Iterable[MultiMap[K, V]]) =
      maps.foldLeft(MultiMap.empty[K, V])(_ <> _)



  case class Slurp(node: Node):
    def entry(kind: Entry.Kind, path: List[names.Component], name: names.Component) =
      MultiMap.just(name, Entry(kind, path, name))

    def entries(
      path: List[names.Component],
      binding: Node.Binding
    ): MultiMap[names.Component, Entry] = binding match
      case b: Node.Binding.Equation =>
        entry(Entry.Equation, path, b.lhs)
      case b: Node.Binding.Subnode =>
        entry(Entry.Subnode, path, b.subnode)
      case b: Node.Binding.Merge =>
        val children = b.cases.map { case (k,n) => entries(path, n) }
        MultiMap.concat(children)
      case b: Node.Binding.Reset =>
        entries(path, b.nested)

    def entries(path: List[names.Component], nested: Node.Nested): MultiMap[names.Component, Entry] =
      val entry    = this.entry(Entry.Nested, path, nested.context)
      val pathX    = path :+ nested.context
      val children = nested.children.map(entries(pathX, _))
      entry <> MultiMap.concat(children)

    def entries(): MultiMap[names.Component, Entry] =
      entries(List(), node.nested)

    /** Get entries that this variable depends on. */
    def dependencies(mpEntries: MultiMap[names.Component, Entry], var_ : Exp.Var): SortedSet[Entry] =
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
              throw new except.VariableNoBindingException(node.path, var_, ess)

    def dependencies(entries: MultiMap[names.Component, Entry], exp: Exp): SortedSet[Entry] =
      val vs = term.Compound.take.vars(exp)
      val ds = vs.flatMap(dependencies(entries, _))
      SortedSet.from(ds)

    def dependencies(
      entries: MultiMap[names.Component, Entry],
      flow: Flow
    ): SortedSet[Entry] = flow match
      case Flow.Pure(e) =>
        dependencies(entries, e)
      case Flow.Arrow(first, later) =>
        dependencies(entries, first) ++ dependencies(entries, later)
      case Flow.Pre(e) =>
        SortedSet.empty
      case Flow.Fby(_, e) =>
        SortedSet.empty

    def dependencies(
      mpEntries: MultiMap[names.Component, Entry],
      path: List[names.Component],
      binding: Node.Binding
    ): MultiMap[Entry, Entry] = binding match
      case b: Node.Binding.Equation =>
        MultiMap(Entry(Entry.Equation, path, b.lhs) -> dependencies(mpEntries, b.rhs))
      case b: Node.Binding.Subnode =>
        val depss = b.args.map(dependencies(mpEntries, _))
        val deps  = depss.foldLeft(SortedSet.empty)(_ ++ _)
        MultiMap(Entry(Entry.Subnode, path, b.subnode) -> deps)
      case b: Node.Binding.Merge =>
        // find all entries with definition in any of b.cases
        // PERF store this on node or nested
        val contexts = SortedSet(b.cases.map(_._2.context) : _*)
        val locals = mpEntries.entries.filter { case (k,vs) =>
          vs.exists(p => p.path.exists(contexts.contains(_)))
        }.keySet

        val depss = b.cases.map { case (clock, nested) =>
          // restrict mpEntries
          val mpEntriesX = MultiMap(mpEntries.entries.map { case (k,vs) =>
            if locals.contains(k)
            then k -> vs.filter(v => v.path.contains(nested.context))
            else k -> vs
          })
          val clockD        = dependencies(mpEntriesX, clock)
          val (entry, deps) = dependencies(mpEntriesX, path, nested)
          MultiMap(entry -> clockD) <> deps
        }

        MultiMap.concat(depss)
      case b: Node.Binding.Reset =>
        val clockD        = dependencies(mpEntries, b.clock)
        val (entry, deps) = dependencies(mpEntries, path, b.nested)
        MultiMap(entry -> clockD) <> deps

    def dependencies(
      mpEntries: MultiMap[names.Component, Entry],
      path: List[names.Component],
      nested: Node.Nested
    ): (Entry, MultiMap[Entry, Entry]) =
      val entry    = Entry(Entry.Nested, path, nested.context)
      val pathX    = path :+ nested.context
      val children = nested.children.map(dependencies(mpEntries, pathX, _))
      val depsX    =
        MultiMap.concat(children)
          .entries
          .mapValues { _ + entry }
      (entry, MultiMap(depsX.toSeq : _*))

    def graph(): Graph =
      val mpEntries = entries()
      val (_, deps) = dependencies(mpEntries, List(), node.nested)
      val vertices = mpEntries.entries.values.foldLeft(SortedSet.empty)(_ ++ _)
      Graph(vertices, deps)

  object except:
    class ScheduleException(msg: String) extends Exception(msg)

    class VariableNoBindingException(val node: List[names.Component], val e: Exp.Var, val ess: List[Entry]) extends ScheduleException(
      s"""Qualified variable '${e.pprString}' has invalid entries.
        |This should not happen in a valid program.
        | Node: ${names.Prefix(node).pprString}
        | Sort: ${e.sort.pprString}
        | Entries: ${pretty.tupleP(ess)}
        |""".stripMargin)

    class CycleEntryException(val entry: Entry) extends ScheduleException(
      s"""Cycle: non-causal program.
        | Entries: ${pretty.layout(entry.ppr)}
        |""".stripMargin)

    class CyclePrettyException(val node: List[names.Component], val cycle: Graph.Cycle) extends ScheduleException(
      s"""Cannot schedule node '${names.Prefix(node).pprString}' due to a cyclic dependency.
        |${cycle.pprString}""".stripMargin)
