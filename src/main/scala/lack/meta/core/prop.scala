package lack.meta.core

import lack.meta.base.Integer
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}

object prop:
  enum Form:
    /** Contract precondition.
     *  Term should only refer to inputs and constants.
     */
    case Require
    /** Contract postcondition.
     *  Term should only refer to inputs, outputs and constants.
     */
    case Guarantee
    /** Local assertion.
     *  Term can refer to any variables including locals.
     */
    case Property
    /** Trust me.
     *  Term can refer to any variables including locals.
     */
    case Sorry

    /** Internal contract precondition which has been instantiated to a proof
     * obligation in the caller.
     *  Term should only refer to inputs and constants.
     */
    case SubnodeRequire
    /** Automatically-generated assertion.
     *  Term can refer to any variables including locals.
     */
    case Generated

  case class Judgment(name: String, term: Exp, form: Form):
    def pretty: String = s"${form} ${name}: ${term.pretty}"

    def isObligation: Boolean = form match
      case Form.Require => false
      case Form.Guarantee => true
      case Form.Property => true
      case Form.Sorry => false
      case Form.SubnodeRequire => true
      case Form.Generated => true
