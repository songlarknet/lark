package lark.meta.smt

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty
import lark.meta.core.node.transform.Grate
import lark.meta.core.node.Node
import lark.meta.core.term.{Exp, Val, Eval, Compound, Flow}

import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

case class Trace(steps: List[Trace.Row], invalidates: List[Property], source: Trace.Source) extends pretty.Pretty:
  def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))

  def pprNode(node: Node, options: Trace.Options, assumptionsSet: names.immutable.RefSet, obligationsSet: names.immutable.RefSet): pretty.Doc =
    // TODO: disable slicing for the generated integer-overflow checks. Because
    // these only exist in the system representation, we can't easily slice the
    // original node to see what they refer to. This is a bit dumb. The integer
    // overflow stuff is a bit shonky. It also has issues with overflows in
    // unused parts of ifs (see src/test/scala/lark/examples/bug/IntegerOverflow.scala).
    val noSlicing =
      invalidates.exists(p => !node.props.contains(p.judgment.judgment))
    val slice =
      options.focus match
        case _ if noSlicing => node
        case Trace.Options.FocusMutualInfluence =>
          Grate.influence(node, invalidatesSet, assumptionsSet ++ obligationsSet)
        case Trace.Options.FocusAllProperties =>
          Grate.node(node, assumptionsSet ++ obligationsSet)
        case Trace.Options.FocusFailingProperty =>
          Grate.node(node, invalidatesSet)
        case Trace.Options.FocusEverything =>
          node
    pretty.Colour.Grey.of(pretty.text("Node") <+> node.klass.ppr <> pretty.colon) <@>
    pprNode(slice, names.Prefix(List()), indentDepth = 1, subnodeDepth = 0, steps.map(_ => true), List(), options) <>
    (source match
      case Trace.Counterexample => pretty.emptyDoc
      case Trace.Inductive => pretty.line <>
        "The inductive proof failed without finding a concrete counterexample. " +
        "The above counterexample-to-induction might hint at which invariants " +
        "are missing, but it does not necessarily describe a real execution as " +
        "the trace does not start from an initial state.")

  def pprNode(
    node:   Node,
    prefix: names.Prefix,
    indentDepth:  Int,
    subnodeDepth: Int,
    clock:  List[Boolean],
    args:   List[(names.Component, Exp)],
    options: Trace.Options
  ): pretty.Doc =
    val paramsP = node.vars.filter(_._2.isInput).map { (c,v) =>
      val (argP, e, pfx) = args.find(_._1 == c) match
        case None => (pretty.emptyDoc, node.xvar(c), prefix)
        case Some((_, e)) => (pretty.equal <+> pprX(e, prefix.parent), e, prefix.parent)
      pprI(v.pprNamed(prefix(c)) <> argP, indentDepth) <>
      pprExp(e, pfx, clock, indentDepth)
    }
    val outputsP = node.vars.filter(_._2.isOutput).map { (c,v) =>
      pprI(v.pprNamed(prefix(c)), indentDepth) <>
      pprExp(node.xvar(c), prefix, clock, indentDepth)
    }
    val propsP = node.props.map { p =>
      val exp = node.expOfJudgment(p)
      val values = evals(p.term, prefix)
      val ok =
        values.forall(v => v == Val.Bool(true))
      val colour =
        if ok
        then pretty.Colour.Green
        else pretty.Colour.Red
      val valuesP = values.map { v =>
        if ok
        then v.ppr
        else if v == Val.Bool(false)
        then pretty.Colour.Red.of(v.ppr)
        else pretty.Colour.Yellow.of(v.ppr)
      }

      pprI(p.pprObligationShort <> pretty.colon, indentDepth) <>
      pprI(pprX(exp, prefix), indentDepth + 1, colour) <>
      pprValues(valuesP, clock, indentDepth + 1, colour)
    }
    val nested =
      if subnodeDepth >= options.hideSubnodeBindingsAtDepth
      then outputsP.toSeq ++ pprAbstract(node, node.nested, prefix, indentDepth, subnodeDepth, clock, options) ++ propsP
      else Seq(pprNested(node, node.nested, prefix, indentDepth, subnodeDepth, clock, options)) ++ propsP
    pretty.vsep(paramsP.toSeq ++ nested)

  def pprX(e: Exp, prefix: names.Prefix): pretty.Doc = e match
    case Exp.Cast(_, e) => pprX(e, prefix)
    case Exp.App(_, prim, args*) =>
      pretty.parens(pretty.hsep(prim.ppr +: args.map(pprX(_, prefix))))
    case Exp.Val(v) =>
      Val.unwrap(v).ppr
    case Exp.Var(_, v) =>
      prefix(v).ppr
  def pprX(e: Flow, prefix: names.Prefix): pretty.Doc = e match
    case Flow.Arrow(a, b) =>
      pretty.text("arrow") <> pretty.tuple(List(pprX(a, prefix), pprX(b, prefix)))
    case Flow.Pre(e) =>
      pretty.text("pre") <> pretty.tuple(List(pprX(e, prefix)))
    case Flow.Fby(a, b) =>
      pretty.text("fby") <> pretty.tuple(List(Val.unwrap(a).ppr, pprX(b, prefix)))
    case Flow.Pure(e) => pprX(e, prefix)

  def pprNested(
    node:   Node,
    nested: Node.Nested,
    prefix: names.Prefix,
    indentDepth:  Int,
    subnodeDepth: Int,
    clock:  List[Boolean],
    options: Trace.Options
  ): pretty.Doc =
    val noprops = nested.children.filter { b =>
      b match
        case Node.Binding.Equation(lhs, _) =>
          !node.props.exists(p => p.term == node.xvar(lhs))
        case _ =>
          true
    }
    val ps = noprops.map { b =>
      b match
        case Node.Binding.Equation(lhs, rhs) =>
          val values = evalFlow(prefix(lhs), rhs, nested, prefix)
          pprIRef(prefix(lhs), pretty.equal <+> pprX(rhs, prefix), indentDepth) <>
          pprValues(values.map(_.ppr), clock, indentDepth, pretty.Colour.Yellow)

        case Node.Binding.Subnode(subnode, args) =>
          val sn = node.subnodes(subnode)
          val argsX = sn.params.zip(args)
          val metasP = pretty.tuple(sn.metas.map(m => pretty.text(m.name) <+> pretty.equal <+> pretty.value(m.any)))
          pprI(pretty.text("Subnode") <+> prefix(subnode).ppr <+> pretty.equal <+> sn.klass.pprString <> metasP <> pretty.colon, indentDepth) <>
          pprNode(sn, prefix ++ names.Prefix(List(subnode)), indentDepth + 1, subnodeDepth + 1, clock, argsX, options)
        case Node.Binding.Merge(scrutinee, cases) =>
          pprI(pretty.text("Merge") <> pretty.tuple(List(pprX(scrutinee, prefix))), indentDepth) <>
          pprExp(scrutinee, prefix, clock, indentDepth) <@>
          pretty.vsep(cases.map { (v,nested) =>
            val clockX = evals(scrutinee, prefix).zip(clock).map { (s,c) => s == Val.unwrap(v) && c }
            val indentDepthX = indentDepth + 1
            val header = pretty.text("Match") <> pretty.tupleP(List(Val.unwrap(v)))

            if clockX.exists(c => c)
            then pprI(header, indentDepthX) <> pprNested(node, nested, prefix, indentDepth + 2, subnodeDepth, clockX, options)
            else pprI(header <+> pretty.text("..."), indentDepthX)
          })
        case Node.Binding.Reset(exp, nestedX) =>
          pprI(pretty.text("Reset") <> pretty.tuple(List(pprX(exp, prefix))), indentDepth) <>
          pprExp(exp, prefix, clock, indentDepth) <@>
          pprNested(node, nestedX, prefix, indentDepth + 1, subnodeDepth, clock, options)
    }
    pretty.vsep(ps)


  def pprAbstract(
    node:   Node,
    nested: Node.Nested,
    prefix: names.Prefix,
    indentDepth:  Int,
    subnodeDepth: Int,
    clock:  List[Boolean],
    options: Trace.Options
  ): List[pretty.Doc] =
    nested.children.flatMap { b =>
      b match
        case Node.Binding.Equation(lhs, rhs) =>
          List()

        case Node.Binding.Subnode(subnode, args) =>
          val sn = node.subnodes(subnode)
          val argsX = sn.params.zip(args)
          val metasP = pretty.tuple(sn.metas.map(m => pretty.text(m.name) <+> pretty.equal <+> pretty.value(m.any)))
          val subnodeP = pprI(pretty.text("Subnode") <+> prefix(subnode).ppr <+> pretty.equal <+> sn.klass.pprString <> metasP <> pretty.colon, indentDepth) <>
            pprNode(sn, prefix ++ names.Prefix(List(subnode)), indentDepth + 1, subnodeDepth + 1, clock, argsX, options)
          List(subnodeP)
        case Node.Binding.Merge(scrutinee, cases) =>
          cases.flatMap { (v,nested) =>
            val clockX = evals(scrutinee, prefix).zip(clock).map { (s,c) => s == Val.unwrap(v) && c }
            val indentDepthX = indentDepth + 1

            if clockX.exists(c => c)
            then pprAbstract(node, nested, prefix, indentDepth + 2, subnodeDepth, clockX, options)
            else List()
          }
        case Node.Binding.Reset(exp, nestedX) =>
          pprAbstract(node, nestedX, prefix, indentDepth + 1, subnodeDepth, clock, options)
    }

  def pprIRef(ref: names.Ref, rest: pretty.Doc, depth: Int) =
    pprI(ref.ppr <+> rest, depth)

  def pprI(doc: pretty.Doc, depth: Int, colour: pretty.Colour.Code = pretty.Colour.Grey) =
    pretty.indent(colour.of(doc), depth * 2) <> pretty.line

  def pprValues(valuesP: List[pretty.Doc], clock: List[Boolean], depth: Int, colour: pretty.Colour.Code) =
    val clocked = valuesP.zip(clock).map( (v,c) => if c then v else pprUndefined <> colour.ppr)
    val pre = pretty.text((" " * depth * 2) + " ~~>")
    val ss = pre ::
      (source match
        case Trace.Counterexample => clocked
        case Trace.Inductive      => pretty.text("...") :: clocked)
    colour.of(pretty.hsep(ss.map(pretty.padto(24, _))))

  def pprExpColour(exp: Exp, prefix: names.Prefix, clock: List[Boolean], depth: Int, colour: pretty.Colour.Code) =
    val values = evals(exp, prefix)
    pprValues(values.map(_.ppr), clock, depth, colour)

  def pprExp(exp: Exp, prefix: names.Prefix, clock: List[Boolean], depth: Int) =
    pprExpColour(exp, prefix, clock, depth, pretty.Colour.Yellow)

  def heaps(prefix: names.Prefix): List[Eval.Heap] =
    steps.map { s =>
      (s.heap ++ s.state).flatMap { (r,v) =>
        if r.fullyQualifiedPath.startsWith(prefix.prefix)
        then Some(names.Ref.fromPathUnsafe(r.fullyQualifiedPath.drop(prefix.prefix.length)) -> v)
        else None
      }
    }

  def evals(exp: Exp, prefix: names.Prefix) =
    heaps(prefix).map { heap =>
      try
        Val.unwrap(Eval.exp(heap, exp, Eval.Options(checkRefinement = true)))
      catch
        case _ : Eval.except.RefinementException =>
          new pretty.Pretty:
            def ppr = pprOverflow
    }

  /** Evaluate a flow expression. We could just look its value up in the heap,
   * but the model coming from the SMT solver takes non-deterministic values
   * when there's an integer overflow.
   * We need to re-evaluate the expressions to catch them.
   * We really need to do some kind of taint analysis, because this won't
   * propagate overflows through all bindings as much as it should.
  */
  def evalFlow(ref: names.Ref, flow: Flow, nested: Node.Nested, prefix: names.Prefix) =
    val hps = heaps(prefix)

    hps.zip(None +: hps.map(Some(_))).map { case (heap, pre_heap) =>
      try
        def exp(e: Exp, h: Eval.Heap = heap) =
          Val.unwrap(Eval.exp(h, e, Eval.Options(checkRefinement = true)))
        flow match
          case Flow.Pure(e) => exp(e)
          case Flow.Arrow(a, b) =>
            if heap(nested.INIT.get) == Val.Bool(true)
            then exp(a)
            else exp(b)
          case Flow.Fby(v, e) =>
            pre_heap.map(h => exp(e, h)).getOrElse(heap(ref))
          case Flow.Pre(e) =>
            if heap(nested.INIT.get) == Val.Bool(true)
            then
              new pretty.Pretty:
                def ppr = pprUndefined
            else pre_heap.map(h => exp(e, h)).getOrElse(heap(ref))
      catch
        case e : Eval.except.RefinementException =>
          new pretty.Pretty:
            def ppr = pprOverflow
    }

  val pprUndefined = pretty.Colour.Grey.of("-")
  val pprOverflow  = pretty.Colour.Red.of("overflow")

  def invalidatesSet =
    scala.collection.immutable.SortedSet.from(invalidates.map(_.judgment.consequent))

object Trace:
  sealed trait Source
  case object Counterexample extends Source
  case object Inductive extends Source

  case class Options(
    focus: Options.Focus = Options.FocusMutualInfluence,
    hideSubnodeBindingsAtDepth: Int = 1,
  )

  object Options:
    sealed trait Focus
    case object FocusMutualInfluence extends Focus
    case object FocusAllProperties extends Focus
    case object FocusFailingProperty extends Focus
    case object FocusEverything extends Focus

  case class Row(values: List[(names.Ref, Val)], stateValues: List[(names.Ref, Val)]) extends pretty.Pretty:
    def heap  = scala.collection.immutable.SortedMap.from(values)
    def state = scala.collection.immutable.SortedMap.from(stateValues)
    /** Pretty-print all values in the trace */
    def ppr = names.Namespace.fromSeq(values).ppr

    /** Pretty-print just the top levels of a trace, omitting the deeply-nested
     * values. */
    def pprTruncate(layers: Int) =
      val (internal, external) = values.partition { case (k,v) =>
        val int = k.fullyQualifiedPath.exists { c =>
          names.ComponentSymbol.isInternal(c.symbol)
        }
        val ganky = k.name.symbol.toString == ""
        int || ganky
      }
      val internalX = internal.filter { case (k,v) =>
        k.name.symbol != names.ComponentSymbol.PROP
      }
      pretty.vsep(List(
        names.Namespace.fromSeq(external).pprTruncate(layers),
        pretty.Colour.Grey.of(names.Namespace.fromSeq(internalX).pprTruncate(layers))))

  def fromModel(steps: Int, sexpr: SExpr, judgments: List[Property], source: Trace.Source): Trace =
    def allDefs(s: SExpr): Iterable[(names.Ref, Val)] = s match
      case CommandsResponses.GetModelResponseSuccess(m) =>
        m.flatMap(allDefs)
      case Commands.DefineFun(fd) =>
        if (fd.params.isEmpty) {
          val r = Term.take.ref(fd.name).getOrElse {
            throw new Solver.SolverException(s,
              s"can't parse model counterexample: bad name ${fd.name}")
          }
          val v = Term.take.value(fd.body).getOrElse {
            throw new Solver.SolverException(s,
              s"can't parse model counterexample: bad value ${fd.body}")
          }

          Seq((r, v))
        } else {
          Seq()
        }
      case _ =>
        throw new Solver.SolverException(s, "can't parse model counterexample")

    val ds = allDefs(sexpr)

    def takePrefixed(prefix: names.Prefix): List[(names.Ref, Val)] =
      val pfx = prefix.prefix
      val dsI = ds.filter((k,v) => k.prefix.startsWith(pfx))
      val dsK = dsI.map((k,v) => (k.copy(prefix = k.prefix.drop(pfx.length)), v))
      val dsS = dsK.toArray.sortBy(_._1).toList
      dsS

    val stepD = for (i <- 0 to steps) yield {
      val row   = takePrefixed(Prove.rowPrefix(i))
      val state = takePrefixed(Prove.statePrefix(i))
      Row(row, state)
    }

    val bads  = judgments.filter { prop =>
      stepD.exists { step =>
        step.heap(prop.judgment.consequent) match
          case Val.Bool(b) => !b
          case _ => false
      }
    }

    Trace(stepD.toList, bads, source)
