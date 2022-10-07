package lack.test.core.target.c.exp

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Eval
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.Sort

import lack.meta.core.target.c.{Printer => Pr}
import lack.meta.core.target.C

import lack.test.hedgehog._
import lack.test.suite._

import lack.test.core.target.c.Cbmc

import scala.collection.immutable.SortedMap

/** C code gen test: generate expressions and check C code against our evaluator */
class P extends HedgehogSuite:
  val g = lack.test.core.term.exp.G(lack.test.core.term.prim.G())

  property("bounded is as bounded does", grind = Some(100), withConfig = p => p.copy(discardLimit = hedgehog.core.DiscardCount(1000))) {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s    <- g.sort.runtime.all.ppr("sort")

      e    <- g.raw(env, s).ppr("e")
      eX   <- Property.try_ {
        term.Bounded.bound(e).annotated
      }.ppr("eX")

      heap <- g.val_.heap(env).ppr("heap")

      vX <- Property.try_ {
        Eval.exp(heap, eX, Eval.Options(checkRefinement = true))
      }.ppr("vX")

      v <- Property.ppr(Eval.exp(heap, eX, Eval.Options(checkRefinement = true)), "v")
    yield
      Result.assert(v == vX)
  }

  property("raw expressions eval OK (refines enabled & discarded)", grind = Some(100), withConfig = p => p.copy(discardLimit = hedgehog.core.DiscardCount(1000))) {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s    <- g.sort.runtime.all.ppr("sort")

      e    <- g.raw(env, s).ppr("e")
      eX   <- Property.try_ {
        term.Bounded.bound(e).annotated
      }.ppr("eX")

      heap <- g.val_.heap(env).ppr("heap")

      v <- Property.try_ {
        Eval.exp(heap, eX, Eval.Options(checkRefinement = true))
      }.ppr("v")

      self = pretty.text("NO_SELF_ACCESS")
      binds =
        for (k, v) <- heap
        yield Pr.Type.sort(v.sort) <+> Pr.Ident.component(k.name) <+> pretty.equal <+> C.Term.val_(v) <> pretty.semi
      asserts =
        for
          (e,i) <- List(eX).zipWithIndex
          vi = pretty.text("$$") <> pretty.value(i)
          expect =
            s match
              // Use approximate equality for floats. This only makes sense for
              // continuous expressions but hopefully expressions with
              // branching won't be too near the threshold.
              case Sort.Real =>
                Pr.Term.fun("lack_float_approx", List(vi, C.Term.val_(v)))
              case _ =>
                vi <+> pretty.text("==") <+> C.Term.val_(v)
        yield
          Pr.Type.sort(s) <+> vi <+> pretty.equal <+>
            C.Term.exp(self, e) <> pretty.semi <@>
            Pr.Term.fun("assert", List(expect)) <> pretty.semi

      code <- Property.ppr(pretty.vsep(
        binds.toList ++ List(pretty.emptyDoc) ++ asserts.toList
      ), "code")
    yield
      checkMain(code)
  }

  test("example") {
    check("int main() { assert(true); }")
  }

  def checkMain(stms: pretty.Doc) =
    check(
      pretty.text("int main() {") <@>
        pretty.indent(stms) <@>
      pretty.text("}"))

  def check(code: pretty.Doc) =
    val options =
      C.Options(basename = "example", classes = SortedMap.empty)
    val doc =
      C.prelude(options) <@>
      code
    Cbmc.check(doc)
