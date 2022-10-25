package lark.meta.smt

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty
import lark.meta.core.term.Val

import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

case class Trace(steps: List[Trace.Row]) extends pretty.Pretty:
  def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))

  def pprTruncate(layers: Int = 2) = // (node: Node, trace: Trace) : pretty.Doc =
    val stepsP = steps.zipWithIndex.map { case (step,i) =>
      pretty.text("Step") <+> pretty.value(i) <> pretty.colon <@>
      pretty.indent(step.pprTruncate(layers))
    }
    pretty.vsep(stepsP)

  def propertyKnownFalse(prop: names.Ref): Boolean =
    steps.exists { r =>
      r.map(prop) match
        case Val.Bool(b) => !b
        case _ => false
    }

object Trace:
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

  def fromModel(steps: Int, sexpr: SExpr): Trace =
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

    Trace(stepD.toList)
