package lack.meta.smt

import lack.meta.base.{names, num}
import smtlib.Interpreter
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

object term:

  /** Apply function to all symbols in term.
   */
  def mapSSymbol(t: Terms.Term)(f: Terms.SSymbol => Terms.SSymbol): Terms.Term =
    // PERF: tail-call, stack overflow
    def go(t: Terms.Term): Terms.Term = t match
      case Terms.QualifiedIdentifier(id, sort) =>
        Terms.QualifiedIdentifier(id.copy(symbol = f(id.symbol)), sort)
      case Terms.FunctionApplication(fun, terms) =>
        Terms.FunctionApplication(fun, terms.map(go))
      case _ : Terms.Constant =>
        t

      case Terms.AnnotatedTerm(tt, attr, attrs) =>
        Terms.AnnotatedTerm(go(tt), attr, attrs)
      case Terms.Let(d, ds, body) =>
        val dx  = Terms.VarBinding(f(d.name), go(d.term))
        val dxs = ds.map(dd => Terms.VarBinding(f(dd.name), go(dd.term)))
        Terms.Let(dx, dxs, go(body))
      case Terms.Forall(d, ds, body) =>
        val dx  = Terms.SortedVar(f(d.name), d.sort)
        val dxs = ds.map(dd => Terms.SortedVar(f(dd.name), dd.sort))
        Terms.Forall(dx, dxs, go(body))
      case Terms.Exists(d, ds, body) =>
        val dx  = Terms.SortedVar(f(d.name), d.sort)
        val dxs = ds.map(dd => Terms.SortedVar(f(dd.name), dd.sort))
        Terms.Exists(dx, dxs, go(body))

      case _ : Terms.TermExtension =>
        assert(false, s"mapSymbol: can't map over support term extensions. got term: ${t}")

    go(t)

  /** Non-capture-avoiding substitution. */
  def renamePrefix(old: names.Prefix, neu: names.Prefix, t: Terms.Term): Terms.Term =
    val substOld = old.pprString + "."
    val substNew = neu.pprString + "."
    def rename(sym: Terms.SSymbol) =
      val str = sym.name
      val idx =
        if str.startsWith(substOld) then
          substNew + str.drop(substOld.length)
        else
          str
      Terms.SSymbol(idx)

    mapSSymbol(t)(rename)


  /** Hack: pretty-print expression with each top-level 'and' clause on a
   * separate line. This is slightly easier to read, but I should make a nicer
   * pretty-printer.
   */
  def pprTermBigAnd(t: Terms.Term): String = t match
    case Terms.FunctionApplication(f, args) if f.id.symbol.name == "and" =>
      val xs = args.map(x => s"    ${x}").mkString("\n")
      s"(and\n$xs)"
    case _ => t.toString

  object compound:
    def sym(s: String) =
      Terms.SSymbol(s)
    def id(s: String) =
      Terms.Identifier(sym(s))

    def qid(s: String, sort: Terms.Sort): Terms.QualifiedIdentifier =
      Terms.QualifiedIdentifier(id(s), Some(sort))
    def qid(s: String): Terms.QualifiedIdentifier =
      Terms.QualifiedIdentifier(id(s))

    def qid(s: names.Ref, sort: Terms.Sort): Terms.QualifiedIdentifier =
      qid(s.pprString, sort)
    def qid(s: names.Ref): Terms.QualifiedIdentifier =
      qid(s.pprString)

    def funapp(f: String, args: Terms.Term*) = (f, args.toList) match
      case ("ite", List(p, t, f)) => ite(p, t, f)
      case ("and", args) => and(args : _*)
      case ("or", args) => or(args : _*)
      case ("=>", List(ante, con)) => implies(ante, con)
      case ("not", List(p)) => not(p)
      case ("=", List(a, b)) => equal(a, b)
      case _ => funappNoSimp(f, args.toList)

    def funappNoSimp(f: String, args: List[Terms.Term]): Terms.Term =
      Terms.FunctionApplication(qid(f), args)

    def and(args: Terms.Term*) =
      def go(t: Terms.Term): Seq[Terms.Term] = t match
        case Terms.QualifiedIdentifier(ti, _)
         if ti.symbol.name == "true" => Seq()
        case Terms.FunctionApplication(qi, args)
          if qi.id.symbol.name == "and" => args.flatMap(go)
        case _ => Seq(t)

      val argsX = args.flatMap(go)
      argsX match
        case Seq() => bool(true)
        case Seq(i) => i
        case _ => funappNoSimp("and", argsX.toList)

    def or(args: Terms.Term*) =
      def go(t: Terms.Term): Seq[Terms.Term] = t match
        case Terms.QualifiedIdentifier(ti, _)
         if ti.symbol.name == "false" => Seq()
        case Terms.FunctionApplication(qi, args)
          if qi.id.symbol.name == "or" => args.flatMap(go)
        case _ => Seq(t)

      val argsX = args.flatMap(go)
      argsX match
        case Seq() => bool(false)
        case Seq(i) => i
        case _ => funappNoSimp("or", argsX.toList)

    def ite(p: Terms.Term, t: Terms.Term, f: Terms.Term) = take.bool(p) match
      case Some(true) => t
      case Some(false) => f
      case _ => funappNoSimp("ite", List(p, t, f))

    def implies(ante: Terms.Term, con: Terms.Term) = (take.bool(ante), take.bool(con)) match
      case (Some(true), _) => con
      case (Some(false), _) => bool(true)
      case (_, Some(true)) => bool(true)
      case (_, Some(false)) => ante
      case _ => funappNoSimp("=>", List(ante, con))

    def not(p: Terms.Term) = take.bool(p) match
      case Some(b) => compound.bool(!b)
      case _ => funappNoSimp("not", List(p))

    def equal(a: Terms.Term, b: Terms.Term) = funappNoSimp("=", List(a, b))

    def int(i: num.Integer) =
      // cvc5 barfs on negative integers. Is this standards-compliant?
      if (i >= 0)
        Terms.SNumeral(i)
      else
        funappNoSimp("-", List(Terms.SNumeral(- i)))

    def real(f: Float) =
      Terms.SDecimal(BigDecimal.decimal(f))

    def bool(b: Boolean) = qid(b.toString)


  object take:
    def bool(t: Terms.Term): Option[Boolean] = t match
      case Terms.QualifiedIdentifier(ti, _)
        if ti.symbol.name == "true" => Some(true)
      case Terms.QualifiedIdentifier(ti, _)
        if ti.symbol.name == "false" => Some(false)
      case _ => None