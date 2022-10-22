package lark.meta.source.node

import lark.meta.base.num.Integer
import lark.meta.base.{names, pretty}
import lark.meta.core
import lark.meta.source.Stream
import lark.meta.source.Stream.SortRepr
import lark.meta.source.Compound

import scala.collection.mutable
import scala.reflect.ClassTag

class Invocation(val instance: names.Ref, val builder: Builder):

  /** Check if the invocation has been used to construct a node previously */
  private[source]
  var _used: Boolean = false
  private[source]
  def markUsed(): Unit =
    _used = true

  /** Check if the invocation has had any information added by the user,
   * (such as the arguments being specified).
   * If _empty is true, then the user probably forgot to add the arguments.
   */
  var _empty: Boolean = true
  /** Mark the invocation as filled - the user has explicitly provided some
   * information. Consumers usually want to use one of the safe functions
   * `sort`, `meta` or `stream` to provide extra information about the node
   * being invoked. However, if there really are no arguments at all, then the
   * user can call this. */
  def unsafeFill(): Invocation =
    _empty = false
    this

  val metas:    mutable.ArrayBuffer[core.node.Meta] = mutable.ArrayBuffer()
  val arguments: mutable.ArrayBuffer[core.term.Exp] = mutable.ArrayBuffer()

  // TODO keep track of meta-level arguments
  def sort[T: SortRepr](name: String): Unit =
    unsafeFill()
    metas += core.node.Meta(name, summon[SortRepr[T]].sort)
  def meta[T](name: String, value: T)(using location: lark.meta.macros.Location): T =
    unsafeFill()
    metas += core.node.Meta(name, value)
    value

  /** Mark an expression as an argument to a subnode.
   *
   * If you have a node you want to call which looks something like:
   * > class SoFar(e: Stream[Bool]) extends Node
   * then you might try to call it from another node as:
   * > SoFar(x > 5)
   *
   * However, the problem with the above call is that the subnode gets directly
   * instantiated with any occurrences of e replaced with the value `x > 5`,
   * losing the fact that e referred to the first parameter. This substitution
   * makes it hard to do modular proofs: if SoFar has some local propositions
   * that we'd like to prove, but all we have is a few different instances of
   * SoFar with different arguments, then it becomes hard to know which parts
   * of the proof can be reused across the different instances.
   * Copilot has a similar problem with this "eager substitution", which is why
   * they don't support contracts for modular proofs.
   *
   * We get around this by requiring the invocation to explicitly mark the
   * parameters that will be substituted for argument values. We bundle this up
   * inside a "Invocation" object which is passed to the Node base class
   * like so:
   * > class SoFar(e: Stream[Bool], invocation: Invocation) extends Node(invocation)
   *
   * Then, you can call it by calling builder.invoke:
   * > def sofar(e: Stream[Bool])(using builder: Builder): SoFar =
   * >  builder.invoke { invocation =>
   * >    new SoFar(invocation.stream("e", e))
   * >  }
   *
   * This requires some extra boilerplate for each node definition. In the future
   * it should be relatively straightforward to have a macro generate these invocations
   * from the class constructor.
   */
  def stream[T](name: String, argvalue: Stream[T]): Stream[T] =
    unsafeFill()
    val v = builder.nodeRef.fresh(
      names.ComponentSymbol.fromScalaSymbol(name),
      core.node.Variable(argvalue.sort, lark.meta.macros.Location.empty, core.node.Variable.Argument))
    arguments += argvalue._exp
    new Stream[T](v)(using argvalue.sortRepr)

object Invocation:
  class EmptyException(val base: Base, val invocation: Invocation, message: String) extends Exception(message)

  // HACK: hack to allow user-defined compound types in args.
  // This should be a typeclass and the magic stuff can be cleaned up when the source language is baked
  // Also needs to deal with outputs/local variables
  trait Freshen:
    def freshen(name: String, invocation: Invocation): Freshen
