package lark.meta.core.node.analysis.equivalence

import lark.meta.base.{pretty, names, debug}
import lark.meta.base.names.given
import lark.meta.base.collection.MultiMap
import lark.meta.base.collection.mutable.EGraph
import lark.meta.base.collection.mutable.EGraph.Tree

import lark.meta.core
import lark.meta.core.Sort
import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow, Compound, Val, Prim, prim}
import lark.meta.core.node
import lark.meta.core.node.Node
import lark.meta.core.node.analysis.Equivalence
import lark.meta.core.node.analysis.Equivalence.Op

import scala.collection.immutable
import scala.collection.mutable

/** Rule definitions:
  *
  * Here we have the rewrite rules that we apply to the equivalence graph.
  * These definitions aren't pretty or fancy, but they should be OK for now.
  * I don't think the de Moura e-matching machine supports variadic rules,
  * so we're stuck with some kind of ad-hackery for `pre(f(e...))` kind of
  * rules anyway.
  */
object Rewrite:
  /** Boring rules: these rules are applied to both graphs. They're
   * basically the rules that we expect the SMT solver to know about. There's
   * no point in us telling the SMT solver anything about these rules, but we
   * want to apply them anwyay because they may expose opportunities for the
   * interesting rules.
  */
  object Boring extends RuleSet:
    /** Commutative primitives `x ⊙ y = y ⊙ x` */
    val commutative = Set[Prim](
      prim.Table.Add,
      prim.Table.And,
      prim.Table.Eq,
      prim.Table.Mul,
      prim.Table.Or
    )
    /** Associative primitives `x ⊙ (y ⊙ z) = (x ⊙ y) ⊙ z` */
    val associative = Set[Prim](
      prim.Table.Add,
      prim.Table.And,
      prim.Table.Mul,
      prim.Table.Or
    )
    /** Identities `x ⊙ v = x` */
    val identity = Map[Prim, Set[Val]](
      prim.Table.Add -> Set(Val.Real(0), Val.Int(0)),
      prim.Table.And -> Set(Val.Bool(true)),
      prim.Table.Mul -> Set(Val.Real(1), Val.Int(1)),
      prim.Table.Or  -> Set(Val.Bool(false))
    )
    /** "Cancelling out" `x ⊙ v = v` */
    val cancel = Map[Prim, Set[Val]](
      prim.Table.And -> Set(Val.Bool(false)),
      prim.Table.Mul -> Set(Val.Real(0), Val.Int(0)),
      prim.Table.Or  -> Set(Val.Bool(true))
    )

    add("commutative") { k =>
      for
        (Op.Prim(p), l1, l2) <- take.binop(k)
        if commutative.contains(p)
      yield
        make.prim(p, l2, l1)
    }

    // PERF: This rule might cause an explosion. Maybe we want to generalise
    // binary associative operators to n-ary with some normalised order instead
    // of having an explicit rule here.
    add("associative") { k =>
      for
        (Op.Prim(p),  l1, k23) <- take.binop(k)
        (Op.Prim(pX), l2, l3)  <- take.binop(k23)
        if p == pX && associative.contains(p)
        if Seq(l1, k23, l2, l3).distinct.length == 4
      yield
        make.prim(p, make.prim(p, l1, l2), l3)
    }

    add("right-identity") { k =>
      for
        (Op.Prim(p),  l1, l2) <- take.binop(k)
        v                     <- take.val_(l2)
        if identity.contains(p) && identity(p).contains(v)
      yield
        l1
    }

    add("right-cancel") { k =>
      for
        (Op.Prim(p),  l1, l2) <- take.binop(k)
        v                     <- take.val_(l2)
        if cancel.contains(p) && cancel(p).contains(v)
      yield
        l2
    }

    add("const-propagation") { k =>
      for
        (p, args) <- take.prim(k)
        vss = args.map(take.val_(_))
        vs  = vss.flatMap(_.headOption)
        if vs.length == args.length
      yield
        make.val_(p.eval(vs))
    }

  /** Interesting rules talk about the things that the SMT solver wouldn't know
   * or aren't obvious after translating to a transition system.
  */
  object Interesting extends RuleSet:
    // VAR x stuck
    // VAL v stuck
    // PRIM REWRITE RULES:
    // we could rewrite prims:
    // f(e -> e', ...)
    // f(pre(e), ...)
    // but the other direction of these rules are a bit simpler
    // PRE REWRITE RULES:
    // pre(x) stuck
    // pre(v):
    // Maybe this is a boring rule: it should be obvious from transition system
    add("pre(v) = v") { k =>
      for
        arg      <- take.pre(k)
        v        <- take.val_(arg)
      yield
        arg
    }
    // pre(prim)
    add("pre(f(e0, e1, ...)) = f(pre(e0), pre(e1), ...)") { k =>
      for
        arg      <- take.pre(k)
        (p,args) <- take.prim(arg)
      yield
        make.prim(p, args.map(make.pre(_))*)
    }
    // pre(pre(e)) stuck
    // pre(arrow(e, e')) stuck
    // pre(µ. e ... µ0):
    // I'm not sure whether there are any rewrites related to this.
    // pre(µ0) stuck
    // ARROW REWRITE RULES:
    // arrow(e,e) = e
    // Maybe this is a boring rule: it should be obvious from transition system
    add("arrow(e, e) = e") { k =>
      for
        (l1, l2) <- take.arrow(k)
        if l1 == l2
      yield
        l1
    }
    // arrow(prim, prim)
    // I think this is the wrong way around - it's not really exposing opportunities
    add("arrow(f(e0, e1, ...), f(e0', e1', ...)) = f(arrow(e0, e0'), arrow(e1, e1'), ...)") { k =>
      for
        (l1, l2) <- take.arrow(k)
        (p1,args1) <- take.prim(l1)
        (p2,args2) <- take.prim(l2)
        if p1 == p2
        if args1.length == args2.length
        argsX = args1.zip(args2).map { (a1,a2) => make.arrow(a1, a2) }
      yield
        make.prim(p1, argsX*)
    }
    // arrow(µ. ..., ...) ?
    // arrow(µ0, ...) ?
    // TODO: also want arrow(arrow(x, y), z) = arrow(x, z)
    // TODO: also want arrow(x, arrow(y, z)) = arrow(x, z)

    // RECURSIVE REWRITE RULES:
    // This is the most interesting, and least conventional (?) of the rules.
    // If we have a recursive computations that performs two
    // associative and commutative operations, we can split it into two:
    // > (µ. a ⊙ b -> a' ⊙ b' ⊙ pre µ0)
    // > ==rewrite=> if µ0 not in free a, a', b, b'
    // > (µ. a -> a' ⊙ pre µ0) ⊙ (µ. b -> b' ⊙ pre µ0)
    //
    // The actual rewrites are a slight variation on this, because we want to
    // ensure that it introduces only equalities that refer to state variables
    // as they are better suited to extracting invariants.
    // We have two similar rewrites. Unfortunately we need both because the
    // treatment of `(z -> pre x)` and `fby(z, x)` are slightly different.
    // > (µ. z -> pre ((a ⊙ b) ⊙ µ0))
    // > ==rewrite=>
    // > (µ. z -> pre (a ⊙ µ0)) ⊙ (µ. z -> pre (b ⊙ µ0))
    add("🐱 go µ: (µ. z -> pre (a ⊙ µ0))") { k =>
      for
        body <- take.muBinder(k)
        (z, preabmu) <- take.arrow(body)
        zv <- take.val_(z)
        abmu <- take.pre(preabmu)
        (p, List(ab, mu)) <- take.prim(abmu)
        if Boring.associative.contains(p)
        if Boring.commutative.contains(p)
        if Boring.identity.contains(p) && Boring.identity(p).contains(zv)
        (pab, List(a, b)) <- take.prim(ab)
        if pab == p
        _ <- take.muRef0(mu)
        if !summon[RuleApp].refersToMu0(a)
        if !summon[RuleApp].refersToMu0(b)
      yield
        make.prim(p,
          make.muBinder(make.arrow(z, make.pre(make.prim(p, a, mu)))),
          make.muBinder(make.arrow(z, make.pre(make.prim(p, b, mu)))))
    }
    // > (µ. pre ((a ⊙ b) ⊙ (z -> µ0)))
    // > ==rewrite=>
    // > (µ. pre (a ⊙ (z -> µ0))) ⊙ (µ. pre (b ⊙ (z -> µ0)))
    add("🐱 go µ: (µ. pre (a ⊙ (z -> µ0)))") { k =>
      for
        body <- take.muBinder(k)
        abzmu <- take.pre(body)
        (p, List(ab, zmu)) <- take.prim(abzmu)
        if Boring.associative.contains(p)
        if Boring.commutative.contains(p)
        (pab, List(a, b)) <- take.prim(ab)
        if pab == p
        (z, mu) <- take.arrow(zmu)
        zv <- take.val_(z)
        if Boring.identity.contains(p) && Boring.identity(p).contains(zv)
        _ <- take.muRef0(mu)
        if !summon[RuleApp].refersToMu0(a)
        if !summon[RuleApp].refersToMu0(b)
      yield
        make.prim(p,
          make.muBinder(make.pre(make.prim(p, a, make.arrow(z, mu)))),
          make.muBinder(make.pre(make.prim(p, b, make.arrow(z, mu)))))
    }


  class RuleApp(val graph: EGraph[Op], val classes: mutable.SortedMap[EGraph.Id, mutable.HashSet[EGraph.Node[Op]]]):
    def getClass(k: EGraph.Id): mutable.HashSet[EGraph.Node[Op]] =
      // TODO: XXX: HACK: e-graphs are messed up
      classes.getOrElse(graph.find(k), mutable.HashSet())

    /** Check if a certain class mentions µ0 */
    def refersToMu0(k: EGraph.Id): Boolean =
      refersToMu(k, 0, mutable.HashSet())
    def refersToMu(k: EGraph.Id, level: Int, seen: mutable.HashSet[EGraph.Id]): Boolean =
      if seen.contains(k)
      then false
      else
        seen += k
        getClass(k).exists { n => n.op match
          // Named, bound variables cannot refer to µ0 - short circuit
          case Op.Var(_) =>
            return false
          case Op.MuVar(levelX) =>
            return level == levelX
          case Op.MuBinder =>
            n.children.exists { kX =>
              refersToMu(k, level + 1, seen)
            }
          case _ =>
            n.children.exists { kX =>
              refersToMu(k, level, seen)
            }
        }

  class RuleSet:
    val rules = mutable.ArrayBuffer[(String, EGraph.Id => RuleApp ?=> Seq[EGraph.Id])]()
    def add(name: String)(body: EGraph.Id => RuleApp ?=> Seq[EGraph.Id]): Unit =
      rules += ((name, body))

    /** Run a single match/subst-all step for all rules.
     * This doesn't rebuild after merging the graph - the graph is left in a
     * dirty state.
     */
    def step(graph: EGraph[Op]): Unit =
      val classes = graph.classes
      given RuleApp = RuleApp(graph, classes)
      val matches = mutable.ArrayBuffer[(String, EGraph.Id, EGraph.Id)]()
      rules.foreach { (name, body) =>
        classes.foreach { (k, _) =>
          body(k).foreach { result =>
            if result != k
            then matches += ((name, k, result))
          }
        }
      }

      // Rebuild classes for logging
      val classesX = graph.classes
      matches.foreach { (name, k, result) =>
        graph.merge(k, result)
      }

  /** Helpers for matching left-hand-side */
  object take:
    def unop(k: EGraph.Id)(using ruleApp: RuleApp): Seq[(Op, EGraph.Id)] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.children match
          case List(arg) => Some((n.op, arg))
          case _ => None
      }

    def binop(k: EGraph.Id)(using ruleApp: RuleApp): Seq[(Op, EGraph.Id, EGraph.Id)] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.children match
          case List(arg1, arg2) => Some((n.op, arg1, arg2))
          case _ => None
      }

    def var_(k: EGraph.Id)(using ruleApp: RuleApp): Seq[names.Ref] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.op match
          case Op.Var(v) =>
            Some(v)
          case _ => None
      }

    def val_(k: EGraph.Id)(using ruleApp: RuleApp): Seq[Val] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.op match
          case Op.Val(v) =>
            Some(v)
          case _ => None
      }

    def muBinder(k: EGraph.Id)(using ruleApp: RuleApp): Seq[EGraph.Id] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.op match
          case Op.MuBinder =>
            Some(n.children.head)
          case _ => None
      }

    def muRef0(k: EGraph.Id)(using ruleApp: RuleApp): Seq[Unit] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.op match
          case Op.MuVar(0) =>
            Some(())
          case _ => None
      }

    def prim(k: EGraph.Id)(using ruleApp: RuleApp): Seq[(Prim, List[EGraph.Id])] =
      ruleApp.getClass(k).toSeq.flatMap { n =>
        n.op match
          case Op.Prim(p) =>
            Some((p, n.children))
          case _ => None
      }

    def pre(k: EGraph.Id)(using ruleApp: RuleApp): Seq[EGraph.Id] =
      unop(k).flatMap { (op,arg) =>
        if op == Op.Pre
        then Some(arg)
        else None
      }

    def arrow(k: EGraph.Id)(using ruleApp: RuleApp): Seq[(EGraph.Id, EGraph.Id)] =
      binop(k).flatMap { (op, arg1, arg2) =>
        if op == Op.Arrow
        then Some(arg1, arg2)
        else None
      }

  /** Helpers for constructing right-hand-side */
  object make:
    def node(op: Op, args: EGraph.Id*)(using ruleApp: RuleApp): EGraph.Id =
      ruleApp.graph.add(op, args*)

    def var_(r: names.Ref)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.Var(r))
    def val_(v: Val)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.Val(v))
    def prim(p: Prim, args: EGraph.Id*)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.Prim(p), args*)
    def pre(arg: EGraph.Id)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.Pre, arg)
    def arrow(arg1: EGraph.Id, arg2: EGraph.Id)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.Arrow, arg1, arg2)
    def muBinder(arg: EGraph.Id)(using ruleApp: RuleApp): EGraph.Id =
      node(Op.MuBinder, arg)
    def muRef0(using ruleApp: RuleApp): EGraph.Id =
      node(Op.MuVar(0))
