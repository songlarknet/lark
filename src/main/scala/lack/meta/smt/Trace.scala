package lack.meta.smt

import lack.meta.base.names
import lack.meta.base.names.given
import lack.meta.base.pretty
import lack.meta.core.term.Val

import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

case class Trace(steps: List[Trace.Row]) extends pretty.Pretty:
  def ppr = pretty.indent(pretty.vsep(steps.map(_.ppr)))
object Trace:
  case class Row(values: List[(names.Ref, Val)]) extends pretty.Pretty:
    def ppr = pretty.braces(pretty.csep(values.map((k,v) => k.ppr <+> pretty.equal <+> v.ppr)))
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
      val pfx = Check.rowPrefix(i).prefix
      val dsI = ds.filter((k,v) => k.prefix.startsWith(pfx))
      val dsK = dsI.map((k,v) => (k.copy(prefix = k.prefix.drop(pfx.length)), v))
      val dsF = dsK.filter((k,v) => !names.ComponentSymbol.isInternal(k.name.symbol))
      val dsS = dsF.toArray.sortBy(_._1).toList
      Row(dsS)
    }

    Trace(stepD.toList)
