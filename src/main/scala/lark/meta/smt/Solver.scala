package lark.meta.smt

import lark.meta.smt.Term.compound
import smtlib.Interpreter
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import smtlib.interpreters.{CVC4Interpreter, Z3Interpreter}

class Solver(interpreter: Interpreter, verbose: Boolean, definePrelude: Boolean = true):
  if (definePrelude)
    Solver.preludeCommands.map(command(_))

  var fresh: Int = 0

  def command(cmd: SExpr): SExpr =
    val r = commandUnchecked(cmd)
    r match
      case _ : CommandsResponses.Error =>
        throw new Solver.SolverException(r)
      case _ =>
        r

  def commandUnchecked(cmd: SExpr): SExpr =
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
      // The Scala smtlib parser doesn't seem to handle sat, unsat or unknown results from check-sat-assuming.
      // When it tries to parse the result it encounters an error that looks like:
      //  (error "Solver encountered exception: smtlib.parser.Parser$UnexpectedTokenException: Unexpected token at position: (74, 1). Expected: [OParen]. Found: unsat")
      //
      if (e.msg.contains("UnexpectedTokenException"))
        if (e.msg.endsWith("Found: unsat"))
          CommandsResponses.CheckSatStatus(CommandsResponses.UnsatStatus)
        else if (e.msg.endsWith("Found: sat"))
          CommandsResponses.CheckSatStatus(CommandsResponses.SatStatus)
        else if (e.msg.endsWith("Found: unknown"))
          CommandsResponses.CheckSatStatus(CommandsResponses.UnknownStatus)
        else
          e
      else
        e
    case _ => response

  def declareConst(name: Terms.SSymbol, sort: Terms.Sort): Unit =
    val r = command(Commands.DeclareConst(name, sort))
    if (!r.isInstanceOf[CommandsResponses.Success.type])
      throw new Solver.SolverException(r, s"declareConst ${name} ${sort}: expected success, but got:")

  def declareConsts(consts: Iterable[Terms.SortedVar]): Unit = consts.foreach { c =>
    declareConst(c.name, c.sort)
  }

  def assert(term: Terms.Term): SExpr =
    command(Commands.Assert(term))

  def checkSat(): CommandsResponses.CheckSatStatus =
    command(Commands.CheckSat()).asInstanceOf[CommandsResponses.CheckSatStatus]

  /** Check satisfaction assuming that some expression is true.
    */
  def checkSatAssumingX[T](prop: Terms.Term)(cont: CommandsResponses.CheckSatStatus => T): T =
    val actlit  = compound.sym(s"%actlit$fresh")
    val xactlit = Terms.QualifiedIdentifier(Terms.Identifier(actlit))
    fresh = fresh + 1
    declareConst(actlit, Terms.Sort(compound.id("Bool")))
    assert(compound.implies(xactlit, prop))
    val sat = command(Commands.CheckSatAssuming(Seq(Commands.PropLiteral(actlit, true))))
    if (sat.isInstanceOf[CommandsResponses.CheckSatStatus])
      val ret = cont(sat.asInstanceOf[CommandsResponses.CheckSatStatus])
      assert(compound.not(xactlit))
      ret
    else
      throw new Solver.SolverException(sat)

  /** Execute in a local push/pop context
    */
  def pushed[T](cont: => T): T =
    command(Commands.Push(1))
    try
      cont
    finally
      command(Commands.Pop(1))

  var freed = false
  def free() =
    if !freed then
      interpreter.free()
      freed = true

  override def finalize() =
    free()

object Solver:
  def gimme(verbose: Boolean = false): Solver = new Solver(interpreters.z3(), verbose)

  object interpreters:
    def z3() = Z3Interpreter.buildDefault
    def cvc5() = new CVC4Interpreter("cvc5",
      Array("--lang", "smt2",
        "--incremental",
        "--produce-models",
        "--print-success"),
      tailPrinter = true)

  class SolverException(response: SExpr, message: String = "SMT solver returned unexpected response") extends Exception(
    s"""${message}
      ${response}""")


  /** Helper functions used by the translation.
   * Division in SMTlib is total, but uses some undefined value-dependent
   * result for division by zero. So (5 / 0) and (6 / 0) both have values,
   * but they're not necessarily the same. This makes it pretty hard to show
   * that the evaluator semantics agree with the SMT.  Isabelle defines
   * division-by-zero to be equal to zero, so we wrap division to do that
   * instead.
   *
   * SMTLib's integer division also has interesting rounding behaviour, so we
   * wrap it to agree with the C and evaluator semantics. Maybe later, when we
   * run into proof issues, we could expose the raw SMT division.
   */
  val preludeCommands: List[Commands.Command] =
    import Term.compound._
    val Int = Terms.Sort(compound.id("Int"))
    val Real = Terms.Sort(compound.id("Real"))
    val m = sym("m")
    val n = sym("n")
    val mm = qid("m")
    val nn = qid("n")

    // Safe division on natural numbers
    val ndiv =
      Commands.DefineFun(Commands.FunDef(sym("lark_div_Nat"),
        List(Terms.SortedVar(m, Int), Terms.SortedVar(n, Int)),
        Int,
        ite(
          equal(nn, int(0)),
          int(0),
          funapp("div", mm, nn))))

    // Safe division on signed integers. Wrap SMTLib "div" to round to 0.
    // https://smtlib.cs.uiowa.edu/theories-Ints.shtml:
    //  * "Regardless of sign of m,
    //  *   when n is positive, (div m n) is the floor of the rational number m/n;
    //  *   when n is negative, (div m n) is the ceiling of m/n.
    val idiv =
      Commands.DefineFun(Commands.FunDef(sym("lark_div_Int"),
        List(Terms.SortedVar(m, Int), Terms.SortedVar(n, Int)),
        Int,
        ite(
          equal(nn, int(0)),
          int(0),
          ite(funapp(">", mm, int(0)),
            funapp("div", mm, nn),
            funapp("-", funapp("div", funapp("-", mm), nn))))))

    val rdiv =
      Commands.DefineFun(Commands.FunDef(sym("lark_div_Real"),
        List(Terms.SortedVar(m, Real), Terms.SortedVar(n, Real)),
        Real,
        ite(equal(nn, real(0)), real(0), funapp("/", mm, nn))))

    List(ndiv, idiv, rdiv)
