package lack.test.target.c.exp

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.core.term
import lack.meta.core.term.Check
import lack.meta.core.term.Eval
import lack.meta.core.term.Exp
import lack.meta.core.term.Val
import lack.meta.core.Sort
import lack.meta.core.obc.Obc

import lack.meta.target.c.Cbmc
import lack.meta.target.c.{Printer => Pr}
import lack.meta.target.C

import lack.test.hedgehog._
import lack.test.suite._

import scala.collection.immutable.SortedMap

/** C code gen test: generate expressions and check C code against our evaluator */
class P extends HedgehogSuite:
  val g = lack.test.core.term.exp.G(lack.test.core.term.prim.G())

  property("expressions C matches eval, no overflow") {
    for
      env  <- g.sort.env(Range.linear(1, 10), lack.test.core.sort.G.runtime.all).ppr("env")
      s    <- g.sort.runtime.all.ppr("sort")
      e    <- g.raw(env, s).ppr("e")
      heap <- g.val_.heap(env).ppr("heap")

      // Check that entire expression evaluates with no overflows; discard otherwise
      _ <- Property.try_ {
        Eval.exp(heap, e, Eval.Options(checkRefinement = true))
      }

      // Reconstruct bounded-precision types from expression
      bound   = term.Bounded.bound(e)
      // The expression printer requires the "self" variable for expressions
      // that touch the local class' state, but our expressions don't need it.
      self    = pretty.text("ERROR_NO_SELF")
      // Print heap as C variable bindings
      binds   =
        for (k, v) <- heap
        yield Pr.Type.sort(v.sort) <+> Pr.Ident.component(k.name) <+> pretty.equal <+> Pr.Term.val_(v) <> pretty.semi
      // For each subexpression in the expression e, evaluate it separately
      // and add an assertion that the generated C code has the corresponding
      // value.
      asserts =
        for
          (b,i) <- term.Bounded.allSubexpressions(bound).reverse.zipWithIndex
          v      = Eval.exp(heap, b.annotated, Eval.Options())
          xi     = pretty.text("$$") <> pretty.value(i)
          assign =
            Pr.Type.sort(b.repr) <+> xi <+> pretty.equal <+>
              C.Term.exp(self, b.annotated) <> pretty.semi
        yield
          assign <@>
            Pr.Stm.assertEquals(xi, Pr.Term.val_(v), s)

      code <- Property.ppr(pretty.vsep(
        binds.toList ++ List(pretty.emptyDoc) ++ asserts.toList
      ), "code")
    yield
      checkMain(code)
  }

  def checkMain(stms: pretty.Doc) =
    check(
      pretty.text("int main() {") <@>
        pretty.indent(stms) <@>
      pretty.text("}"))

  def check(code: pretty.Doc) =
    val options =
      C.Options(basename = "test", program = Obc.Program(List()))
    val doc =
      C.prelude(options) <@>
      code
    Cbmc.check(doc)
