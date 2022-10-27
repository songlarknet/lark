package lark.meta.smt

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty
import lark.meta.core.node.transform.Slice
import lark.meta.core.node.Node
import lark.meta.core.term.{Exp, Val}

import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

case class Trace(steps: List[Trace.Row], invalidates: List[Property], source: Trace.Source) extends pretty.Pretty:
  def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))

  def pprNode(node: Node): pretty.Doc =
    // TODO use a recursive slice that looks inside each node
    // TODO slice should include input arguments that are mentioned, bug in Schedule.Graph
    val slice = Slice.node(node, invalidatesSet.map(_.name))
    pretty.text("Node") <+> node.klass.ppr <> pretty.colon <@>
    pprNode(slice, names.Prefix(List()), depth = 1, steps.map(_ => true))

  def pprNode(
    // TODO take in argument expressions, display here 
    node:   Node,
    prefix: names.Prefix,
    depth:  Int,
    clock:  List[Boolean]
  ): pretty.Doc =
    val paramsP = node.vars.filter(_._2.isInput).map { (c,v) =>
      pprI(v.pprNamed(c), depth) <>
      pprRef(prefix(c), clock, depth)
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
          // LODO pretty-print with C pretty-printer
          val colour =
            if invalidates.exists(p => p.judgment.consequent == prefix(lhs))
            then pretty.Colour.Red
            else pretty.Colour.Grey
          pprI(colour.of(prefix(lhs).ppr <+> pretty.equal <+> rhs.ppr), depth) <>
          pprRef(prefix(lhs), clock, depth)
        case Node.Binding.Subnode(subnode, args) =>
          val sn = node.subnodes(subnode)
          val snX = Slice.node(sn)
          val argsP = pretty.tuple(sn.metas.map(m => pretty.text(m.name) <+> pretty.equal <+> pretty.value(m.any)) ++ args.map(_.ppr))
          pprI(pretty.text("Subnode") <+> prefix(subnode).ppr <+> pretty.equal <+> sn.klass.pprString <> argsP <> pretty.colon, depth) <>
          pprNode(snX, prefix ++ names.Prefix(List(subnode)), depth + 1, clock)
        case Node.Binding.Merge(scrutinee, cases) =>
          pprI(pretty.text("Merge") <> pretty.tupleP(List(scrutinee)), depth) <>
          pprExp(scrutinee, clock, depth) <@>
          pretty.vsep(cases.map { (v,nested) =>
            pprI(pretty.text("Match") <> pretty.tupleP(List(v)), depth + 1) <>
            // TODO subclocks
            pprNested(node, nested, prefix, depth + 2, clock)
          })
        case Node.Binding.Reset(exp, nestedX) =>
          pprI(pretty.text("Reset") <> pretty.tupleP(List(exp)), depth) <>
          pprExp(exp, clock, depth) <@>
          // TODO subclocks
          pprNested(node, nestedX, prefix, depth + 1, clock)
    }
    pretty.vsep(ps)

  def pprI(doc: pretty.Doc, depth: Int) =
    pretty.Colour.Grey.of(pretty.indent(doc, depth * 2)) <> pretty.line

  def pprRef(ref: names.Ref, clock: List[Boolean], depth: Int) =
    val colour =
      if invalidates.exists(p => p.judgment.consequent == ref)
      then pretty.Colour.Red
      else pretty.Colour.Yellow
    val pre = pretty.text((" " * depth * 2) + " ~~>")
    val ss = pre :: steps.zip(clock).map( (r,c) => if c then r.map(ref).ppr else pretty.text("-"))
    colour.of(pretty.hsep(ss.map(pretty.padto(24, _))))

  def pprExp(exp: Exp, clock: List[Boolean], depth: Int) = exp match
    case Exp.Var(_, ref) => pprRef(ref, clock, depth)
    case _ => pretty.emptyDoc // TODO eval

  def invalidatesSet =
    scala.collection.immutable.SortedSet.from(invalidates.map(_.judgment.consequent))

object Trace:
  sealed trait Source
  case object Counterexample extends Source
  case object Inductive extends Source

  case class Row(values: List[(names.Ref, Val)]) extends pretty.Pretty:
    def map = values.toMap
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

    val stepD = for (i <- 0 to steps) yield {
      val pfx = Prove.rowPrefix(i).prefix
      val dsI = ds.filter((k,v) => k.prefix.startsWith(pfx))
      val dsK = dsI.map((k,v) => (k.copy(prefix = k.prefix.drop(pfx.length)), v))
      val dsF = dsK // dsK.filter((k,v) => !names.ComponentSymbol.isInternal(k.name.symbol))
      val dsS = dsF.toArray.sortBy(_._1).toList
      Row(dsS)
    }

    val bads  = judgments.filter { prop =>
      stepD.exists { step =>
        step.map(prop.judgment.consequent) match
          case Val.Bool(b) => !b
          case _ => false
      }
    }

    Trace(stepD.toList, bads, source)
