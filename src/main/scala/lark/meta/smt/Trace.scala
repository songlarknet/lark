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

  def pprNode(node: Node, options: Trace.Options, allPropertiesSet: names.immutable.RefSet): pretty.Doc =
    val slice =
      options.focus match
        case Trace.Options.FocusAllProperties =>
          Grate.node(node, allPropertiesSet)
        case Trace.Options.FocusFailingProperty =>
          Grate.node(node, invalidatesSet)
        case Trace.Options.FocusEverything =>
          node
    pretty.text("Node") <+> node.klass.ppr <> pretty.colon <@>
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
      val argP = args.find(_._1 == c) match
        case None => pretty.emptyDoc
        case Some((_, e)) => pretty.equal <+> e.ppr
      pprI(v.pprNamed(c) <> argP, indentDepth) <>
      pprExp(node.xvar(c), prefix, clock, indentDepth)
    }
    val outputsP = node.vars.filter(_._2.isOutput).map { (c,v) =>
      val argP = args.find(_._1 == c) match
        case None => pretty.emptyDoc
        case Some((_, e)) => pretty.equal <+> e.ppr
      pprI(v.pprNamed(c) <> argP, indentDepth) <>
      pprExp(node.xvar(c), prefix, clock, indentDepth)
    }
    val nested =
      if subnodeDepth >= options.hideSubnodeBindingsAtDepth
      then outputsP.toSeq ++ pprAbstract(node, node.nested, prefix, indentDepth, subnodeDepth, clock, options)
      else Seq(pprNested(node, node.nested, prefix, indentDepth, subnodeDepth, clock, options))
    pretty.vsep(paramsP.toSeq ++ nested)

  def pprNested(
    node:   Node,
    nested: Node.Nested,
    prefix: names.Prefix,
    indentDepth:  Int,
    subnodeDepth: Int,
    clock:  List[Boolean],
    options: Trace.Options
  ): pretty.Doc =
    val ps = nested.children.map { b =>
      b match
        case Node.Binding.Equation(lhs, rhs) =>
          def pprX(e: Exp) = lark.meta.target.C.Term.exp("state", e)
          rhs match
            case Flow.Pure(e) =>
              pprIRef(prefix(lhs), pretty.equal <+> pprX(e), indentDepth) <>
              pprExp(node.xvar(lhs), prefix, clock, indentDepth)
            case Flow.Arrow(a, b) =>
              pprIRef(prefix(lhs), pretty.equal <+> "arrow" <> pretty.tuple(List(pprX(a), pprX(b))), indentDepth) <>
              pprExp(node.xvar(lhs), prefix, clock, indentDepth)
            case Flow.Fby(v, e) =>
              pprIRef(prefix(lhs), pretty.equal <+> "fby" <> pretty.tuple(List(Val.unwrap(v).ppr, pprX(e))), indentDepth) <>
              pprExp(node.xvar(lhs), prefix, clock, indentDepth)
            case Flow.Pre(e) =>
              val inits  = steps.map(s => nested.INIT.fold(Val.Bool(false))(i => s.state(prefix(i))))
              val clockX = clock.zip(inits).map { (c,i) => c && i == Val.Bool(false) }
              pprIRef(prefix(lhs), pretty.equal <+> "pre" <> pretty.tuple(List(pprX(e))), indentDepth) <>
              pprExp(node.xvar(lhs), prefix, clockX, indentDepth)

        case Node.Binding.Subnode(subnode, args) =>
          val sn = node.subnodes(subnode)
          val argsX = sn.params.zip(args)
          val metasP = pretty.tuple(sn.metas.map(m => pretty.text(m.name) <+> pretty.equal <+> pretty.value(m.any)))
          pprI(pretty.text("Subnode") <+> prefix(subnode).ppr <+> pretty.equal <+> sn.klass.pprString <> metasP <> pretty.colon, indentDepth) <>
          pprNode(sn, prefix ++ names.Prefix(List(subnode)), indentDepth + 1, subnodeDepth + 1, clock, argsX, options)
        case Node.Binding.Merge(scrutinee, cases) =>
          pprI(pretty.text("Merge") <> pretty.tupleP(List(scrutinee)), indentDepth) <>
          pprExp(scrutinee, prefix, clock, indentDepth) <@>
          pretty.vsep(cases.map { (v,nested) =>
            val clockX = evals(scrutinee, prefix).zip(clock).map { (s,c) => Val.unwrap(s) == Val.unwrap(v) && c }
            val indentDepthX = indentDepth + 1
            val header = pretty.text("Match") <> pretty.tupleP(List(v))

            if clockX.exists(c => c)
            then pprI(header, indentDepthX) <> pprNested(node, nested, prefix, indentDepth + 2, subnodeDepth, clockX, options)
            else pprI(header <+> pretty.text("..."), indentDepthX)
          })
        case Node.Binding.Reset(exp, nestedX) =>
          pprI(pretty.text("Reset") <> pretty.tupleP(List(exp)), indentDepth) <>
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
            val clockX = evals(scrutinee, prefix).zip(clock).map { (s,c) => Val.unwrap(s) == Val.unwrap(v) && c }
            val indentDepthX = indentDepth + 1

            if clockX.exists(c => c)
            then pprAbstract(node, nested, prefix, indentDepth + 2, subnodeDepth, clockX, options)
            else List()
          }
        case Node.Binding.Reset(exp, nestedX) =>
          pprAbstract(node, nestedX, prefix, indentDepth + 1, subnodeDepth, clock, options)
    }

  def pprIRef(ref: names.Ref, rest: pretty.Doc, depth: Int) =
    val colour =
      if invalidates.exists(p => p.judgment.consequent == ref)
      then pretty.Colour.Red
      else pretty.Colour.Grey
    pprI(colour.of(ref.ppr <+> rest), depth)

  def pprI(doc: pretty.Doc, depth: Int) =
    pretty.Colour.Grey.of(pretty.indent(doc, depth * 2)) <> pretty.line

  def pprExp(exp: Exp, prefix: names.Prefix, clock: List[Boolean], depth: Int) =
    val values = evals(exp, prefix)
    val fv = Compound.take.vars(exp)
    val colour =
      if invalidates.exists(p => fv.exists(v => p.judgment.consequent == v.v))
      then pretty.Colour.Red
      else pretty.Colour.Yellow
    val valuesP = values.zip(clock).map( (v,c) => if c then v.ppr else pretty.text("-"))
    val pre = pretty.text((" " * depth * 2) + " ~~>")
    val ss = pre ::
      (source match
        case Trace.Counterexample => valuesP
        case Trace.Inductive      => pretty.text("...") :: valuesP)
    colour.of(pretty.hsep(ss.map(pretty.padto(24, _))))


  def evals(exp: Exp, prefix: names.Prefix) =
    steps.map { s =>
      val heap = s.heap.flatMap { (r,v) =>
        if r.fullyQualifiedPath.startsWith(prefix.prefix)
        then Some(names.Ref.fromPathUnsafe(r.fullyQualifiedPath.drop(prefix.prefix.length)) -> v)
        else None
      }
      Eval.exp(heap, exp, Eval.Options(checkRefinement = false))
    }

  def invalidatesSet =
    scala.collection.immutable.SortedSet.from(invalidates.map(_.judgment.consequent))

object Trace:
  sealed trait Source
  case object Counterexample extends Source
  case object Inductive extends Source

  case class Options(
    focus: Options.Focus = Options.FocusFailingProperty,
    hideSubnodeBindingsAtDepth: Int = 1,
  )

  object Options:
    sealed trait Focus
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
