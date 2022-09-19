package lack.meta.core

import lack.meta.base.pretty
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}
import lack.meta.macros.Location

object prop:
  /** The kind of assertion a judgment is making */
  sealed trait Form
  object Form:
    /** Guarantee or ensure: the node is guaranteeing some property, which we
     * can check as a proof obligation. */
    case object Guarantee extends Form
    /** Rely or assume: the node relies on the environment to provide some
     * property, which we could check at the call-site. */
    case object Rely extends Form
    /** Sorry or trusted: the node has some reason to believe that this
     * assertion is true in all possible contexts, and so it does not need
     * to be checked anywhere. */
    case object Sorry extends Form

  /** The syntactic form used to declare a judgment. Mainly for debugging. */
  sealed trait Syntax extends pretty.Pretty:
    def ppr = pretty.value(this)
    def form: Form
  object Syntax:
    /** Contract precondition.
     *  Term should only refer to inputs and constants.
     */
    case object Require extends Syntax:
      def form = Form.Rely
    /** Contract postcondition.
     *  Term should only refer to inputs, outputs and constants.
     */
    case object Guarantee extends Syntax:
      def form = Form.Guarantee
    /** Local checked assertion.
     *  Term can refer to any variables including locals.
     */
    case object Check extends Syntax:
      def form = Form.Guarantee
    /** Trust me.
     *  Term can refer to any variables including locals.
     */
    case object Sorry extends Syntax:
      def form = Form.Sorry

    /** Automatically-generated assertion.
     *  Term can refer to any variables including locals.
     */
    case class Generated(form: Form) extends Syntax

    object Generated:
      val check = Generated(Form.Guarantee)
      val rely  = Generated(Form.Rely)
      val sorry = Generated(Form.Sorry)

  case class Judgment(name: String, term: Exp, syntax: Syntax, location: Location) extends pretty.Pretty:
    def ppr =
      syntax.ppr <>
      pretty.parens(
        pretty.text(name) <>
        location.ppr(pretty.space)) <>
      pretty.colon <+>
      pretty.indent(term.ppr)

    def form: Form = syntax.form
