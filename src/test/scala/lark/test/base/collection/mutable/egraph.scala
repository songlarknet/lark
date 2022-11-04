package lark.test.base.collection.mutable.egraph

import lark.test.hedgehog._
import lark.test.suite._

import lark.meta.base.collection.mutable.EGraph

sealed trait Prim
object Prim:
  case object Plus extends Prim
  case class Var(id: String) extends Prim
  case class Value(i: Int) extends Prim

case class Exp(prim: Prim, args: Seq[Exp]):
  def equiv(g: EGraph[Prim]): g.Class =
    g.add(prim, args.map(_.equiv(g))*)

  def +(that: Exp): Exp =
    Exp.plus(this, that)

object Exp:
  def plus(args: Exp*) = Exp(Prim.Plus, args)
  def int(i: Int) = Exp(Prim.Value(i), Seq())
  def var_(id: String) = Exp(Prim.Var(id), Seq())

/** Just unit tests for now, writing properties requires a bit more thought */
class P extends HedgehogSuite:
  test("(1 + 2) = 3") {
    val g = new EGraph[Prim]()

    val c1  = Exp.int(1).equiv(g)
    val c2  = Exp.int(2).equiv(g)
    val lhs = (Exp.int(1) + Exp.int(2)).equiv(g)
    val c3  = Exp.int(3).equiv(g)
    val rhs = Exp.int(3).equiv(g)

    assert(c3 == rhs)
    val classes = Seq(c1, c2, lhs, c3)
    assert(classes.distinct == classes)
    assert(classes.map(g.find(_)) == classes)

    val m3 = g.merge(lhs, rhs)
    val m3lr = Seq(m3, lhs, rhs)
    assert(m3lr.map(g.find(_)).distinct == Seq(m3))
    val c123 = Seq(c1, c2, c3)
    assert(c123.map(g.find(_)).distinct == c123.map(g.find(_)))

    g.rebuild()

    assert(m3lr.map(g.find(_)).distinct == Seq(m3))
    assert(c123.map(g.find(_)).distinct == c123.map(g.find(_)))
  }

  test("merge-then-add") {
    val g = new EGraph[Prim]()

    val x  = Exp.var_("x")
    val v0 = Exp.int(0)
    val v1 = Exp.int(1)

    // x = x + 0
    g.merge(
      x.equiv(g),
      (x + v0).equiv(g))

    // x
    val cx   = x.equiv(g)
    // x + 0
    val cx0  = (x + v0).equiv(g)
    // (x + 0) + 0
    val cx00 = g.add(Prim.Plus, cx0, v0.equiv(g))

    assert(cx == cx0)
    assert(cx == cx00)

    g.rebuild()

    assert(g.find(cx) == g.find(cx0))
    assert(g.find(cx) == g.find(cx00))
  }

  test("congruence") {
    val g = new EGraph[Prim]()

    val x  = Exp.var_("x")
    val y  = Exp.var_("y")
    val v0 = Exp.int(0)
    val v1 = Exp.int(1)
    val v2 = Exp.int(2)

    // x + 1 = 1 + x
    g.merge(
      (x + v1).equiv(g),
      (v1 + x).equiv(g)
    )
    // 1 + (1 + y) = (2 + y)
    g.merge(
      (v1 + (v1 + y)).equiv(g),
      (v2 + y).equiv(g)
    )
    g.rebuild()

    assert(x.equiv(g) != y.equiv(g))

    // After merging we can immediately see that x == y, but we don't have
    // the more complex `(1 + (x + 1)) = (2 + y)` until we rebuild, as it
    // requires congruence closure.
    g.merge(x.equiv(g), y.equiv(g))
    assert(x.equiv(g) == y.equiv(g))
    assert((v1 + (x + v1)).equiv(g) != (v2 + y).equiv(g))

    g.rebuild()
    assert((v1 + x).equiv(g) == (y + v1).equiv(g))
    assert((v1 + (x + v1)).equiv(g) == (v2 + y).equiv(g))

    assert((v1 + x).equiv(g) != (v2 + y).equiv(g))
  }
