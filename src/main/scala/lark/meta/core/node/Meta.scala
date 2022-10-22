package lark.meta.core.node

import lark.meta.core
import lark.meta.core.term

/** Meta-arguments.
 * Later, figure out the contract we need.
 * We need to support values, lists of values, sorts and functions.
 */
sealed case class Meta(name: String, any: Any)
// object Meta
  /** A nice value meta-argument */
  // case class Val(value: term.Val) extends Meta

  /** A nice value meta-argument */
  // case class Sort(sort: core.Sort) extends Meta

  /** Any other kind of meta-argument, eg functions. */
  // case class Any(any: scala.Any) extends Meta
