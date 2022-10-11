package lack.meta.source.node

import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core
import lack.meta.source.Stream
import lack.meta.source.Stream.SortRepr
import lack.meta.source.Compound

import scala.collection.mutable
import scala.reflect.ClassTag

trait Sugar:
  val base: Base
  given builder: Builder

  protected def local[T: SortRepr](using loc: lack.meta.macros.Location): base.Lhs[T] =
    base.declare(loc.prettyPath, core.node.Variable.Local)

  protected def output[T: SortRepr](using loc: lack.meta.macros.Location): base.Lhs[T] =
    base.declare(loc.prettyPath, core.node.Variable.Output)

  /** Inside a lemma, declare a variable to be universally quantified */
  protected def forall[T: SortRepr](using loc: lack.meta.macros.Location): Stream[T] =
    base.declare(loc.prettyPath, core.node.Variable.Forall)

  protected def check(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    base.bindProperty(core.Prop.Syntax.Check, name)(prop)

  protected def requires(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    base.bindProperty(core.Prop.Syntax.Require, name)(prop)

  protected def guarantees(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    base.bindProperty(core.Prop.Syntax.Guarantee, name)(prop)

  protected def sorry(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    base.bindProperty(core.Prop.Syntax.Sorry, name)(prop)

  extension [T](lhs: base.Lhs[T])
    protected def := (rhs: Stream[T])(using builder: Builder) =
      base.bind(lhs, rhs)

  def subnode[T <: Base : ClassTag](body: Invocation => T)(using builder: Builder, location: lack.meta.macros.Location): T =
    Sugar.subnode(builder)(body)

object Sugar:
  def subnode[T <: Base : ClassTag](builder: Builder)(body: Invocation => T)(using location: lack.meta.macros.Location): T =
    try
      subnodeNoFreshen(builder)(body)
    catch
      case e: Invocation.EmptyException =>
        builder.invokeWithRef(e.invocation.instance, Some(summon[ClassTag[T]].runtimeClass), Some(location)) { i =>
          Magic.freshen(e.base, i)
        }

  def subnodeNoFreshen[T <: Base : ClassTag](builder: Builder)(body: Invocation => T)(using location: lack.meta.macros.Location): T =
    val klass = summon[ClassTag[T]].runtimeClass
    val name  = klass.getSimpleName() // location.enclosing.getOrElse(klass.getSimpleName())
    builder.invoke(name, Some(klass), Some(location))(body)
