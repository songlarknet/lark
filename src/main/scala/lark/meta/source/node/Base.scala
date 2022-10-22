package lark.meta.source.node

import lark.meta.base.num.Integer
import lark.meta.base.{names, pretty}
import lark.meta.core
import lark.meta.source.Stream
import lark.meta.source.Stream.SortRepr
import lark.meta.source.Compound

import scala.collection.mutable
import scala.reflect.ClassTag

/** The base class for defining nodes.
 * This class provides the basic functionality for constructing nodes, without
 * any reflective or macro magic, except for the use of the source location
 * macro. The lark.meta.source.Node interface wraps this with a friendlier
 * interface that requires less boilerplate.
 */
class Base(invocation: Invocation):
  if (invocation._used)
    throw new Exception(
      s"""Node ${this.getClass.getSimpleName()} constructed with an already-used invocation.
         |Something is reusing invocations for multiple nodes, which is not allowed.
         |""".stripMargin)
  if (invocation._empty && Magic.nodeHasArguments(this))
    throw new Invocation.EmptyException(this, invocation,
      s"""Node ${this.getClass.getSimpleName()} constructed with empty invocation.
         |This usually means that you forgot to 'freshen' arguments with `invocation.stream`.
         |If the node really does have no parameters, then you can quiet this error
         |by "filling" the invocation by calling `invocation.unsafeFill`.
         |""".stripMargin)
  invocation.markUsed()

  private val afterConstructorQueue = mutable.Queue[() => Unit]()
  /** Some operations can only be done after the class has been fully
   * constructed. This function registers a callback to run after the
   * constructor has finished.
  */
  def afterConstructor(f: () => Unit): Unit =
    afterConstructorQueue += f

  /** Some things need to wait until after the constructor has run, so when we
   * create a new node, we call finish afterwards. */
  def finish(): Unit =
    afterConstructorQueue.removeAll().foreach { f =>
      f()
    }
    if (afterConstructorQueue.nonEmpty)
      finish()

  given builder: Builder = invocation.builder

  inline given location: lark.meta.macros.Location = lark.meta.macros.location

  /** A left-hand-side that must be given a value. */
  class Lhs[T: SortRepr](_exp: core.term.Exp) extends Stream[T](_exp):
    def v: names.Component = _exp match
      case core.term.Exp.Var(_, v) =>
        require(v.prefix == builder.nodeRef.path)
        v.name
      case _ =>
        assert(false, s"Internal error: bad Lhs[T]: ${_exp} should be a bare variable")

  def declare[T: SortRepr](name: String, mode: core.node.Variable.Mode)(using loc: lark.meta.macros.Location): Lhs[T] =
    val sort = summon[SortRepr[T]].sort
    val v = core.node.Variable(sort, loc, mode)
    new Lhs(builder.nodeRef.fresh(names.ComponentSymbol.fromScalaSymbol(name), v))

  def bindProperty(syntax: core.Prop.Syntax, name: String)(prop: Stream[Stream.Bool])(using loc: lark.meta.macros.Location) =
    val locx = loc <> builder.nodeRef.locate(prop._exp)
    builder.nodeRef.prop(core.Prop.Judgment(name, prop._exp, syntax, locx))

  def bind[T](lhs: Lhs[T], rhs: Stream[T])(using builder: Builder) =
    builder.nested.equation(lhs.v, core.term.Flow.Pure(rhs._exp))

  protected abstract class Merge[T: SortRepr](scrutinee: Stream[T])(using builder: Builder) extends reflect.Selectable:
    val merge = builder.nested.merge()

    abstract class When(target: Stream[T], reset: Stream[Stream.Bool] = Compound.False) extends reflect.Selectable:
      private val when = core.term.Compound.app(core.term.prim.Table.Eq, Merge.this.scrutinee._exp, target._exp)
      given builder: Builder = new Builder(
        Merge.this.builder.nodeRef,
        Some(merge.when(when).reset(reset._exp)))

  protected abstract class Reset(reset: Stream[Stream.Bool])(using superbuilder: Builder) extends reflect.Selectable:
    given builder: Builder = new Builder(
      superbuilder.nodeRef,
      Some(superbuilder.nested.reset(reset._exp)))
