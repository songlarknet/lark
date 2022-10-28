package lark.meta.smt

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty
import lark.meta.core.node.transform.Slice
import lark.meta.core.node.Node
import lark.meta.core.term.{Exp, Val, Eval, Compound, Flow}

import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

case class Trace(steps: List[Trace.Row], invalidates: List[Property], source: Trace.Source) extends pretty.Pretty:
  def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))

  def pprNode(node: Node): pretty.Doc =
    // TODO use a recursive slice that looks inside each node
    // TODO slice should include input arguments that are mentioned, bug in Schedule.Graph
    val slice = Slice.node(node, invalidatesSet.map(_.name))
    pretty.text("Node") <+> node.klass.ppr <> pretty.colon <@>
    pprNode(slice, names.Prefix(List()), depth = 1, steps.map(_ => true), List())

  def pprNode(
    node:   Node,
    prefix: names.Prefix,
    depth:  Int,
    clock:  List[Boolean],
    args:   List[(names.Component, Exp)]
  ): pretty.Doc =
    val paramsP = node.vars.filter(_._2.isInput).map { (c,v) =>
      val argP = args.find(_._1 == c) match
        case None => pretty.emptyDoc
        case Some((_, e)) => pretty.space <> pretty.equal <+> e.ppr
      pprI(v.pprNamed(c) <> argP, depth) <>
      pprExp(node.xvar(c), prefix, clock, depth)
    }
    pretty.vsep(paramsP.toSeq ++ Seq(pprNested(node, node.nested, prefix, depth, clock)))

  def pprNested(
    node:   Node,
    nested: Node.Nested,
    prefix: names.Prefix,
    depth:  Int,
    clock:  List[Boolean]
  ): pretty.Doc =
    val ps = nested.children.map { b =>
      b match
        case Node.Binding.Equation(lhs, rhs) =>
          def pprX(e: Exp) = lark.meta.target.C.Term.exp("state", e)
          rhs match
            case Flow.Pure(e) =>
              pprIRef(prefix(lhs), pretty.equal <+> pprX(e), depth) <>
              pprExp(node.xvar(lhs), prefix, clock, depth)
            case Flow.Arrow(a, b) =>
              pprIRef(prefix(lhs), pretty.equal <+> "arrow" <> pretty.tuple(List(pprX(a), pprX(b))), depth) <>
              pprExp(node.xvar(lhs), prefix, clock, depth)
            case Flow.Fby(v, e) =>
              pprIRef(prefix(lhs), pretty.equal <+> "fby" <> pretty.tuple(List(Val.unwrap(v).ppr, pprX(e))), depth) <>
              pprExp(node.xvar(lhs), prefix, clock, depth)
            case Flow.Pre(e) =>
              val inits  = steps.map(s => nested.INIT.fold(Val.Bool(false))(i => s.state(prefix(i))))
              val clockX = clock.zip(inits).map { (c,i) => c && i == Val.Bool(false) }
              pprIRef(prefix(lhs), pretty.equal <+> "pre" <> pretty.tuple(List(pprX(e))), depth) <>
              pprExp(node.xvar(lhs), prefix, clockX, depth)

        case Node.Binding.Subnode(subnode, args) =>
          val sn = node.subnodes(subnode)
          val snX = Slice.node(sn)
          val argsX = sn.params.zip(args)
          val metasP = pretty.tuple(sn.metas.map(m => pretty.text(m.name) <+> pretty.equal <+> pretty.value(m.any)))
          pprI(pretty.text("Subnode") <+> prefix(subnode).ppr <+> pretty.equal <+> sn.klass.pprString <> metasP <> pretty.colon, depth) <>
          pprNode(snX, prefix ++ names.Prefix(List(subnode)), depth + 1, clock, argsX)
        case Node.Binding.Merge(scrutinee, cases) =>
          pprI(pretty.text("Merge") <> pretty.tupleP(List(scrutinee)), depth) <>
          pprExp(scrutinee, prefix, clock, depth) <@>
          pretty.vsep(cases.map { (v,nested) =>
            val clockX = evals(scrutinee, prefix).zip(clock).map { (s,c) => Val.unwrap(s) == Val.unwrap(v) && c }
            val depthX = depth + 1
            val header = pretty.text("Match") <> pretty.tupleP(List(v))

            if clockX.exists(c => c)
            then pprI(header, depthX) <> pprNested(node, nested, prefix, depth + 2, clockX)
            else pprI(header <+> pretty.text("..."), depthX)
          })
        case Node.Binding.Reset(exp, nestedX) =>
          pprI(pretty.text("Reset") <> pretty.tupleP(List(exp)), depth) <>
          pprExp(exp, prefix, clock, depth) <@>
          pprNested(node, nestedX, prefix, depth + 1, clock)
    }
    pretty.vsep(ps)

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
    val pre = pretty.text((" " * depth * 2) + " ~~>")
    val ss = pre :: values.zip(clock).map( (v,c) => if c then v.ppr else pretty.text("-"))
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
