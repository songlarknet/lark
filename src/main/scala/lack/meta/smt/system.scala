package lack.meta.smt

import lack.meta.base.Integer
import lack.meta.core.names
import lack.meta.core.builder
import lack.meta.core.builder.Node
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}

import lack.meta.smt.solver.Solver
import lack.meta.smt.solver.compound
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.SExpr

import scala.collection.mutable

object system:
  // use SortedMap here instead?
  case class Namespace(
    values: Map[names.Component, Sort] = Map(),
    namespaces: Map[names.Component, Namespace] = Map()):
      def <>(that: Namespace): Namespace =
        val values = that.values.foldLeft(this.values) { case (m,v) =>
          this.values.get(v._1).foreach { u =>
            assert(u == v._2, s"Namespace invariant failure, different sorts ${u} /= ${v._2} for component ${v._1}")
          }
          m + v
        }
        val namespaces = that.namespaces.foldLeft(this.namespaces) { case (m,n) =>
          m.get(n._1) match {
            case None => m + n
            case Some(nn) => m + (n._1 -> (nn <> n._2))
          }
        }
        Namespace(values, namespaces)

  object Namespace:
    def fromRef(ref: names.Ref, sort: Sort): Namespace =
      ref.path match {
        case Nil =>
          Namespace(values = Map(ref.name -> sort))
        case p :: rest =>
          Namespace(namespaces = Map(p -> fromRef(names.Ref(rest, ref.name), sort)))
      }

  case class Prefix(prefix: names.Ref):
    def apply(name: names.Ref): Terms.SSymbol =
      compound.sym(prefix.pretty + "/" + name.pretty)

  /** Oracle supply so that systems can ask for nondeterministic choices from outside,
   * such as re-initialising delays to undefined on reset. */
  class Oracle:
    val oracles: mutable.ArrayBuffer[(Terms.SSymbol, Sort)] = mutable.ArrayBuffer()

    def oracle(prefix: names.Ref, sort: Sort): Terms.SSymbol =
      val i = oracles.length
      val sym = compound.sym(s"?${prefix.pretty}?${i}")
      oracles += (sym -> sort)
      sym

  /** State supply */
  class Supply:
    var stateIx = 0
    def state(): names.Ref =
      // want better state variables
      val ref = names.Ref(List(), names.Component(names.ComponentSymbol.fromInternal("state"), Some(stateIx)))
      stateIx = stateIx + 1
      ref

  trait System[T]:
    def state: Namespace
    def row: Namespace
    def init(oracle: Oracle, state: Prefix): Terms.Term
    def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, T)
    def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term

  object System:
    def pure[T](value: T): System[T] = new System[T]:
      def state: Namespace = Namespace()
      def row: Namespace = Namespace()
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.bool(true)
      def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, T) =
        (compound.bool(true), value)
      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        compound.bool(true)

  extension[T,U] (outer: System[T => U])
    def <*>(that: System[T]): System[U] = new System[U]:
      def state: Namespace = outer.state
      def row: Namespace = outer.row
      def init(oracle: Oracle, state: Prefix): Terms.Term =
        compound.and(
          this.init(oracle, state),
          that.init(oracle, state))
      def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, U) =
        val (xa, f) = outer.extract(oracle, state, row)
        val (xb, t) = that.extract(oracle, state, row)
        (compound.and(xa, xb), f(t))

      def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
        val xa = outer.step(oracle, state, row, stateX)
        val xb = that.step(oracle, state, row, stateX)
        compound.and(xa, xb)

  object translate:
    def sort(s: Sort): Terms.Sort = s match
      case _: Sort.Integral => Terms.Sort(compound.id("Int"))
      case _: Sort.Mod => Terms.Sort(compound.id("Int"))
      case Sort.Bool => Terms.Sort(compound.id("Bool"))

    def value(v: Val): Terms.Term = v match
      case Val.Bool(b) => compound.qid(b.toString)
      case Val.Int(i) => compound.int(i)

    case class Context(init: names.Ref, supply: Supply)

    def expr(context: Context, exp: Exp): System[Terms.Term] = exp match
      case Exp.flow.Arrow(first, later) =>
        val t0 = expr(context, first)
        val t1 = expr(context, later)
        val choice = new System[Terms.Term => Terms.Term => Terms.Term]:
          def state: Namespace = Namespace.fromRef(context.init, Sort.Bool)
          def row: Namespace = Namespace()
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.bool(true)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            val sym = Terms.QualifiedIdentifier(Terms.Identifier(state(context.init)))
            def choose(a: Terms.Term)(b: Terms.Term): Terms.Term =
              compound.funapp("ite", sym, a, b)
            (compound.bool(true), choose)
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.bool(true)
        choice <*> t0 <*> t1

      case Exp.flow.Pre(pre) =>
        val t0 = expr(context, pre)
        // TODO need sort
        val sort = Sort.Bool
        val ref = context.supply.state()
        new System[Terms.Term]:
          def state: Namespace = Namespace.fromRef(ref, sort) <> t0.state
          def row: Namespace = t0.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            // TODO: use an oracle to re-initialise state(ref) every time.
            // This needs the type of pre though. Perhaps all Exp constructors should have type annotations
            // val u = oracle.oracle(ref, pre)
            t0.init(oracle, state)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            (compound.bool(true), Terms.QualifiedIdentifier(Terms.Identifier(state(ref))))
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                Terms.QualifiedIdentifier(Terms.Identifier(stateX(ref))),
                t0.extract(oracle, state, row)._2),
              t0.step(oracle, state, row, stateX))

      case Exp.flow.Fby(v0, pre) =>
        val t0 = expr(context, pre)
        // TODO need sort
        val sort = Sort.Bool
        val ref = context.supply.state()
        new System[Terms.Term]:
          def state: Namespace = Namespace.fromRef(ref, sort) <> t0.state
          def row: Namespace = t0.row
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.and(
              t0.init(oracle, state),
              compound.funapp("=", Terms.QualifiedIdentifier(Terms.Identifier(state(ref))), value(v0.v)))
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            (compound.bool(true), Terms.QualifiedIdentifier(Terms.Identifier(state(ref))))
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.and(
              compound.funapp("=",
                Terms.QualifiedIdentifier(Terms.Identifier(stateX(ref))),
                t0.extract(oracle, state, row)._2),
              t0.step(oracle, state, row, stateX))

      case Exp.nondet.Undefined(sort) =>
        new System[Terms.Term]:
          def state: Namespace = Namespace()
          def row: Namespace = Namespace()
          def init(oracle: Oracle, state: Prefix): Terms.Term =
            compound.bool(true)
          def extract(oracle: Oracle, state: Prefix, row: Prefix) =
            val o = oracle.oracle(state.prefix, sort)
            (compound.bool(true), Terms.QualifiedIdentifier(Terms.Identifier(o)))
          def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
            compound.bool(true)

      case Exp.Val(v) => System.pure(value(v))
      case Exp.Var(v, s) => new System:
        def state: Namespace = Namespace()
        def row: Namespace = Namespace.fromRef(v, s)
        def init(oracle: Oracle, state: Prefix): Terms.Term =
          compound.bool(true)
        def extract(oracle: Oracle, state: Prefix, row: Prefix): (Terms.Term, Terms.Term) =
          val sym = Terms.QualifiedIdentifier(Terms.Identifier(row(v)))
          (compound.bool(true), sym)
        def step(oracle: Oracle, state: Prefix, row: Prefix, stateX: Prefix): Terms.Term =
          compound.bool(true)

      // TODO: applications
      // case Exp.App(prim, args : _*) =>
      //   compound.funapp(prim.pretty, args.map(ppexp(_)) : _*)

    // TODO: nodes, etc

  // class Translate(solver: Solver)

