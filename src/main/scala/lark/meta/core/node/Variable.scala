package lark.meta.core.node

import lark.meta.macros.Location
import lark.meta.base.pretty
import lark.meta.core.Sort

object Variable:
  sealed trait Mode
  case object Argument extends Mode
  case object Forall extends Mode
  case object Local extends Mode
  case object Output extends Mode
  case object Generated extends Mode


case class Variable(sort: Sort, location: Location, mode: Variable.Mode) extends pretty.Pretty:
  def ppr =
    pretty.value(this.mode) <> pretty.colon <+> this.sort.ppr <+> this.location.ppr

  def pprNamed(name: pretty.Pretty) =
    pretty.value(this.mode) <+> name.ppr <> pretty.colon <+> this.sort.ppr <+> this.location.ppr

  def isInput: Boolean =
    mode == Variable.Argument || mode == Variable.Forall

  def isOutput: Boolean =
    mode == Variable.Output
