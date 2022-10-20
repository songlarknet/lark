package lack.meta.source

import lack.meta.core.node.Builder.Nested
import lack.meta.core.node.Builder.Binding.Merge
import lack.meta.core.node.Builder.Binding.Equation
import lack.meta.core.node.Builder.Binding.Subnode
import lack.meta.core.node.Builder.Binding.Reset

/** "Sneaky invariants" */
class Sneaky(nested: Nested):
  def subnodes(name: String): List[Sneaky] =
    nested.children.toList.flatMap {
      case _: Merge => List()
      case _: Equation => List()
      case s: Subnode =>
        if s.subnode.symbol.toString == name
        then List(new Sneaky(nested.node.subnodes(s.subnode).nested))
        else List()
      case _: Reset => List()
    }

  def subnode(name: String): Sneaky =
    val nodes = subnodes(name)
    nodes match
      case List(h) =>
        h
      case _ :: _ =>
        throw new Exception(s"Sneaky: ambiguous subnode: ${nodes.mkString(", ")} all have name $name")
      case Nil =>
        throw new Exception(s"Sneaky: no subnode named $name")

  def variablesCore(name: String): List[lack.meta.core.term.Exp] =
    nested.children.toList.flatMap {
      case _: Merge => List()
      case e: Equation =>
        if e.lhs.symbol.toString == name
        then List(nested.node.xvar(e.lhs))
        else List()
      case s: Subnode => List()
      case _: Reset => List()
    }

  def variables[T: Stream.SortRepr](name: String): List[Stream[T]] =
    val exps = variablesCore(name)
    exps.map(new Stream[T](_))

  def variable[T: Stream.SortRepr](name: String): Stream[T] =
    val vars = variables(name)
    vars match
      case List(v) => v
      case _ :: _ =>
        throw new Exception(s"Sneaky: ambiguous variable: ${vars.mkString(", ")} all have name $name")
      case Nil =>
        throw new Exception(s"Sneaky: no variable named $name")

object Sneaky:
  def apply(builder: node.Builder): Sneaky =
    new Sneaky(builder.nested)

  def forall[T](xs: List[T])(predicate: T => Stream[Stream.Bool])(using builder: node.Builder): Stream[Stream.Bool] =
    import Compound._
    xs.map(predicate).fold(True)(_ && _)