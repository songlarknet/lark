package lack.meta.smt

import lack.meta.base.Integer
import lack.meta.core.builder.Node
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val, Var}

object pretty:
  /** The pretty-printer needs to know whether a step is the initial step or
    * the next step.
    */
  sealed trait StepType
  object StepType:
    /** Initial state. (x -> y) is printed as x. */
    case object Init extends StepType
    /** Non-reset transition. (x -> y) is printed as y. */
    case object Transition extends StepType
    /** Abstract state before a transition.
      * This is used as the start of evaluation for the inductive case.
      * (x -> y) could evaluate to either x or y. */
    case object Free extends StepType

  def checksat(n: Node, count: Int): String =
    val steps = (0 until count).map { i => new Stepped(i, if (i == 0) StepType.Init else StepType.Transition) }
    val ss = steps.map { step => s"${step.nodedeclares(n)}\n${step.nodebinds(n)}\n" }.mkString("")
    ss + "(echo \"check satisfiability. expect sat:\")(check-sat)"

  def bmc(n: Node, count: Int): String =
    val steps = (0 until count).map { i => new Stepped(i, if (i == 0) StepType.Init else StepType.Transition) }
    steps.map { step =>
      s"""|${step.nodedeclares(n)}
          |${step.nodebinds(n)}
          |
          |(declare-const %actlit${step.step} Bool)
          |(assert (=> %actlit${step.step} (or ${n.allPropObligations.map(p => s"(not ${step.ppexp(p.term)})").mkString(" ")})))
          |(echo "check BMC ${step.step}. expect unsat:")
          |(check-sat-assuming (%actlit${step.step}))
          |(assert (not %actlit${step.step}))
          |""".stripMargin
    }.mkString("")


  def kind(n: Node, count: Int): String =
    val steps = (0 to count).map { i => new Stepped(i, if (i == 0) StepType.Free else StepType.Transition) }
    steps.map { step =>
      if (step.step == 0)
        s"""|${step.nodedeclares(n)}
            |${step.nodebinds(n)}
            |
            |(assert (and ${n.allPropObligations.map(p => step.ppexp(p.term)).mkString(" ")}))
            |""".stripMargin
      else
        s"""|${step.nodedeclares(n)}
            |${step.nodebinds(n)}
            |
            |(declare-const %actlit${step.step} Bool)
            |(assert (=> %actlit${step.step} (or ${n.allPropObligations.map(p => s"(not ${step.ppexp(p.term)})").mkString(" ")})))
            |(echo "check k-ind k=${step.step}. expect unsat:")
            |(check-sat-assuming (%actlit${step.step}))
            |(assert (not %actlit${step.step}))
            |(assert (and ${n.allPropObligations.map(p => step.ppexp(p.term)).mkString(" ")}))
            |""".stripMargin
    }.mkString("")


  class Stepped(val step: Integer, val ty: StepType):
    def ppvar(v: Var): String =
      s"${v.pretty}@${step}"

    def ppsort(s: Sort): String = s match
      case _: Sort.Integral => "Int"
      case _: Sort.Mod => "Int"
      case Sort.Bool => "Bool"

    def ppval(v: Val): String = v match
      case Val.Bool(b) => b.toString
      case Val.Int(i) => i.toString
      // TODO

    def ppexp(e: Exp): String = e match
      case Exp.flow.Arrow(first, later) => ty match
        case StepType.Init => ppexp(first)
        case StepType.Transition => ppexp(later)
        case StepType.Free => throw new Exception(s"can't pretty-print expression (x -> y) for StepType.Free ${e}")
      case Exp.flow.Pre(pre) => ty match
        case StepType.Init => throw new Exception(s"can't pretty-print expression (pre e) for StepType.Init ${e}")
        case StepType.Transition => new Stepped(step - 1, ty).ppexp(pre)
        case StepType.Free => throw new Exception(s"can't pretty-print expression (pre e) for StepType.Free ${e}")
      case Exp.Val(v) => ppval(v)
      case Exp.Var(v) => ppvar(v)
      case Exp.App(prim, args : _*) =>
        s"(${prim.pretty} ${args.map(ppexp(_)).mkString(" ")})"

    def declares(vs: List[Var]): String =
      vs.map { v => s"(declare-const ${ppvar(v)} ${ppsort(v.sort)})"}.mkString("\n")

    def bind(lhs: Exp, rhs: Exp): String = rhs match
      case Exp.flow.Arrow(first, later)
        if ty == StepType.Free => s"(assert (or (= ${ppexp(lhs)} ${ppexp(first)}) (= ${ppexp(lhs)} ${ppexp(later)})))"
      case Exp.flow.Pre(pre)
        if ty == StepType.Init => s"; ${ppexp(lhs)} := ${rhs.pretty}, unguarded pre for init (step 0)"
      case Exp.flow.Pre(pre)
        if ty == StepType.Free => s"; ${ppexp(lhs)} := ${rhs.pretty}, unguarded pre for free (pre-transition)"
      case _ => s"(assert (= ${ppexp(lhs)} ${ppexp(rhs)}))"

    def nodedeclares(n: Node): String =
      s"""|${declares(n.vars)}
          |${n.subnodes.map { n => nodedeclares(n) }.mkString("\n")}""".stripMargin

    def nodebinds(n: Node): String =
      s"""|; Node ${n.name}
          |${n.bindings.map { case (l,r) => bind(l, r) }.mkString("\n")}
          |${n.subnodes.map { n => nodebinds(n) }.mkString("\n")}""".stripMargin

