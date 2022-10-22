package lark.meta.source.node

import lark.meta.base.num.Integer
import lark.meta.base.{names, pretty}
import lark.meta.core
import lark.meta.source.Stream
import lark.meta.source.Stream.SortRepr
import lark.meta.source.Compound

import scala.collection.mutable
import scala.reflect.ClassTag

class Builder(val nodeRef: core.node.Builder.Node, nestedO: Option[core.node.Builder.Nested] = None):
  var nested = nestedO.getOrElse(nodeRef.nested)

  def withNesting[T](neu: core.node.Builder.Nested)(f: => T): T =
    val old = nested
    try {
      nested = neu
      f
    } finally {
      nested = old
    }

  def expOfStream[T](it: Stream[T])(using location: lark.meta.macros.Location): core.term.Exp =
    if it == null then throw new NullPointerException(
      s"""Null stream argument
         |    A stream was null, which often means that a variable was referenced
         |    before it has been defined. You may need to reorder bindings so that
         |    variables are defined earlier.
         |  Source location: ${location.pprString}
         |""".stripMargin)
    it._exp


  def memo1[T](it: Stream[T])(f: core.term.Exp => core.term.Flow)(using location: lark.meta.macros.Location): Stream[T] =
    val e   = expOfStream(it)
    val mem = nested.memo(f(e))
    new Stream(mem)(using it.sortRepr)

  def memo2[T](a: Stream[T], b: Stream[T])(f: (core.term.Exp, core.term.Exp) => core.term.Flow)(using location: lark.meta.macros.Location): Stream[T] =
    val mem = nested.memo(f(expOfStream(a), expOfStream(b)))
    new Stream(mem)(using a.sortRepr)

  def memo2x1[T, U, V: SortRepr]
    (a: Stream[T], b: Stream[U])
    (f: (core.term.Exp, core.term.Exp) => core.term.Flow)
    (using location: lark.meta.macros.Location): Stream[V] =
    val sort = summon[SortRepr[V]].sort
    val mem = nested.memo(f(expOfStream(a), expOfStream(b)))
    new Stream(mem)

  def memo3x1[T, U, V, W: SortRepr]
    (a: Stream[T], b: Stream[U], c: Stream[V])
    (f: (core.term.Exp, core.term.Exp, core.term.Exp) => core.term.Flow)
    (using location: lark.meta.macros.Location): Stream[W] =
    val sort = summon[SortRepr[W]].sort
    val mem = nested.memo(f(expOfStream(a), expOfStream(b), expOfStream(c)))
    new Stream(mem)

  /** Call a subnode.
   * Invoking subnodes requires a little bit of indirection, because we want to
   * keep a clear interface between the calling node and the called node.
   * ...
   */
  def invoke[T <: Base: ClassTag](
    name: String,
    klass: Option[Class[_]] = None,
    location: Option[lark.meta.macros.Location] = None
  )(body: Invocation => T): T =
    val instance = nodeRef.freshSubnodeRef(names.ComponentSymbol.fromScalaSymbol(name))
    invokeWithRef(instance, klass, location)(body)

  /** Call a subnode.
   * Invoking subnodes requires a little bit of indirection, because we want to
   * keep a clear interface between the calling node and the called node.
   * ...
   */
  def invokeWithRef[T <: Base: ClassTag](
    instance: names.Ref,
    klass: Option[Class[_]] = None,
    location: Option[lark.meta.macros.Location] = None
  )(body: Invocation => T): T =
    val subpath = instance.fullyQualifiedPath
    val klass      = summon[ClassTag[T]].runtimeClass
    val klassName  = klass.getCanonicalName().split('.')
    val components = klassName.map(names.ComponentSymbol.fromScalaSymbol(_)).map(names.Component(_)).toList
    val klassRef   = names.Ref.fromPathUnsafe(components)

    val subnodeRef = new core.node.Builder.Node(new names.mutable.Supply(subpath), subpath, klassRef)
    val subbuilder = new Builder(subnodeRef)
    val inv = new Invocation(instance = instance, builder = subbuilder)
    val node = body(inv)
    node.finish()
    nested.subnode(instance.name, subnodeRef, inv.arguments.toList)
    subnodeRef.metas ++= inv.metas
    node
