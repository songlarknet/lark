package lack.meta.source.node

import lack.meta.base.num.Integer
import lack.meta.base.{names, pretty}
import lack.meta.core
import lack.meta.source.Stream
import lack.meta.source.Stream.SortRepr
import lack.meta.source.Compound

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

  def memo1[T](it: Stream[T])(f: core.term.Exp => core.term.Flow)(using location: lack.meta.macros.Location): Stream[T] =
    val e   = it._exp
    val mem = nested.memo(f(e))
    new Stream(mem)(using it.sortRepr)

  def memo2[T](a: Stream[T], b: Stream[T])(f: (core.term.Exp, core.term.Exp) => core.term.Flow)(using location: lack.meta.macros.Location): Stream[T] =
    val mem = nested.memo(f(a._exp, b._exp))
    new Stream(mem)(using a.sortRepr)

  def memo2x1[T, U, V: SortRepr]
    (a: Stream[T], b: Stream[U])
    (f: (core.term.Exp, core.term.Exp) => core.term.Flow)
    (using location: lack.meta.macros.Location): Stream[V] =
    val sort = summon[SortRepr[V]].sort
    val mem = nested.memo(f(a._exp, b._exp))
    new Stream(mem)

  def memo3x1[T, U, V, W: SortRepr]
    (a: Stream[T], b: Stream[U], c: Stream[V])
    (f: (core.term.Exp, core.term.Exp, core.term.Exp) => core.term.Flow)
    (using location: lack.meta.macros.Location): Stream[W] =
    val sort = summon[SortRepr[W]].sort
    val mem = nested.memo(f(a._exp, b._exp, c._exp))
    new Stream(mem)

  /** Call a subnode.
   * Invoking subnodes requires a little bit of indirection, because we want to
   * keep a clear interface between the calling node and the called node.
   * ...
   */
  def invoke[T <: Base](
    name: String,
    klass: Option[Class[_]] = None,
    location: Option[lack.meta.macros.Location] = None
  )(body: Invocation => T): T =
    val instance = nodeRef.freshSubnodeRef(names.ComponentSymbol.fromScalaSymbol(name))
    invokeWithRef(instance, klass, location)(body)

  /** Call a subnode.
   * Invoking subnodes requires a little bit of indirection, because we want to
   * keep a clear interface between the calling node and the called node.
   * ...
   */
  def invokeWithRef[T <: Base](
    instance: names.Ref,
    klass: Option[Class[_]] = None,
    location: Option[lack.meta.macros.Location] = None
  )(body: Invocation => T): T =
    val subpath = instance.fullyQualifiedPath
    val subnodeRef = new core.node.Builder.Node(new names.mutable.Supply(subpath), subpath)
    val subbuilder = new Builder(subnodeRef)
    val inv = new Invocation(instance = instance, builder = subbuilder)
    val node = body(inv)
    node.finish()
    nested.subnode(instance.name, subnodeRef, inv.arguments.toList)
    node
