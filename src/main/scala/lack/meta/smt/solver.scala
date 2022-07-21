package lack.meta.smt

import smtlib.Interpreter
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import smtlib.interpreters.Z3Interpreter

object solver:
  def gimme(verbose: Boolean = false): Solver = new Solver(Z3Interpreter.buildDefault, verbose)

  object compound:
    def sym(s: String) = Terms.SSymbol(s)
    def id(s: String) = Terms.Identifier(sym(s))
    def qid(s: String, sort: Terms.Sort) = Terms.QualifiedIdentifier(id(s), Some(sort))
    def qid(s: String) = Terms.QualifiedIdentifier(id(s))
    def funapp(f: String, args: Terms.Term*) = Terms.FunctionApplication(qid(f), args)


  class Solver(interpreter: Interpreter, verbose: Boolean):
    var fresh: Int = 0

    def command(cmd: SExpr): SExpr =
      if (verbose)
        System.err.print(s"[smt]< ${cmd}")
      val got = clean(interpreter.eval(cmd))

      if (verbose)
        got match
          case CommandsResponses.Success =>
          case _ => System.err.print(s"[smt]> ${got}")

      got

    private def clean(response: SExpr): SExpr = response match
      case r : CommandsResponses.CheckSatStatus => r
      case e : CommandsResponses.Error =>
        if (e.msg.endsWith("Found: unsat"))
          CommandsResponses.CheckSatStatus(CommandsResponses.UnsatStatus)
        else if (e.msg.endsWith("Found: sat"))
          CommandsResponses.CheckSatStatus(CommandsResponses.SatStatus)
        else if (e.msg.endsWith("Found: unknown"))
          CommandsResponses.CheckSatStatus(CommandsResponses.UnknownStatus)
        else
          e
      case _ => response

    def declareConst(name: Terms.SSymbol, sort: Terms.Sort): SExpr =
      command(Commands.DeclareConst(name, sort))

    def assert(term: Terms.Term): SExpr =
      command(Commands.Assert(term))

    def checkSat(): CommandsResponses.CheckSatStatus =
      command(Commands.CheckSat()).asInstanceOf[CommandsResponses.CheckSatStatus]

    /** Check satisfaction assuming that some expression is true.
      * 
      */
    def checkSatAssumingX[T](prop: Terms.Term)(cont: CommandsResponses.CheckSatStatus => T): T =
      val actlit  = compound.sym(s"%actlit$fresh")
      val xactlit = Terms.QualifiedIdentifier(Terms.Identifier(actlit))
      fresh = fresh + 1
      declareConst(actlit, Terms.Sort(compound.id("Bool")))
      assert(compound.funapp("=>", xactlit, prop))
      val sat = command(Commands.CheckSatAssuming(Seq(Commands.PropLiteral(actlit, true))))
        .asInstanceOf[CommandsResponses.CheckSatStatus]
      val ret = cont(sat)
      assert(compound.funapp("not", xactlit))
      ret


