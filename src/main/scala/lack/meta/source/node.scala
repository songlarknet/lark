package lack.meta.source

import lack.meta.base.num.Integer
import lack.meta.base.names
import lack.meta.core
import lack.meta.source.Stream
import lack.meta.source.Stream.SortRepr

import scala.collection.mutable
import scala.reflect.ClassTag


abstract class Node(invocation: Node.Invocation):

  given builder: Node.Builder = invocation.builder

  inline given location: lack.meta.macros.Location = lack.meta.macros.location

  protected class Lhs[T: SortRepr](_exp: core.term.Exp) extends Stream[T](_exp):
    def v: names.Component = _exp match
      case core.term.Exp.Var(_, v) =>
        require(v.prefix == builder.nodeRef.path)
        v.name
      case _ =>
        assert(false, s"Internal error: bad Lhs[T]: ${_exp} should be a bare variable")


  protected def declare[T: SortRepr](name: String, mode: core.node.Variable.Mode)(using loc: lack.meta.macros.Location): Lhs[T] =
    val sort = summon[SortRepr[T]].sort
    val v = core.node.Variable(sort, loc, mode)
    new Lhs(builder.nodeRef.fresh(names.ComponentSymbol.fromScalaSymbol(name), v))

  protected def local[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
    declare(loc.prettyPath, core.node.Variable.Local)

  protected def output[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
    declare(loc.prettyPath, core.node.Variable.Output)

  protected def bindProperty(syntax: core.Prop.Syntax, name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    val locx = loc <> builder.nodeRef.locate(prop._exp)
    builder.nodeRef.prop(core.Prop.Judgment(name, prop._exp, syntax, locx))

  protected def check(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    bindProperty(core.Prop.Syntax.Check, name)(prop)

  protected def requires(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    bindProperty(core.Prop.Syntax.Require, name)(prop)

  protected def guarantees(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    bindProperty(core.Prop.Syntax.Guarantee, name)(prop)

  protected def sorry(name: String)(prop: Stream[Stream.Bool])(using loc: lack.meta.macros.Location) =
    bindProperty(core.Prop.Syntax.Sorry, name)(prop)

  protected def bind[T](lhs: Lhs[T], rhs: Stream[T])(using builder: Node.Builder) =
    builder.nested.equation(lhs.v, core.term.Flow.Pure(rhs._exp))

  extension [T](lhs: Lhs[T])
    protected def := (rhs: Stream[T])(using builder: Node.Builder) =
      bind(lhs, rhs)

  protected abstract class Merge(using builder: Node.Builder) extends reflect.Selectable:
    val merge = builder.nested.merge()

    abstract class When(when: Stream[Stream.Bool], reset: Stream[Stream.Bool] = Compound.False) extends reflect.Selectable:
      given builder: Node.Builder = new Node.Builder(
        Merge.this.builder.nodeRef,
        Some(merge.when(when._exp).reset(reset._exp)))

  protected abstract class Reset(reset: Stream[Stream.Bool])(using superbuilder: Node.Builder) extends reflect.Selectable:
    given builder: Node.Builder = new Node.Builder(
      superbuilder.nodeRef,
      Some(superbuilder.nested.reset(reset._exp)))

object Node:
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
    def invokeWithName[T <: Node](name: String)(f: Invocation => T): T =
      val instance = nodeRef.freshSubnodeRef(names.ComponentSymbol.fromScalaSymbol(name))
      val subpath = instance.fullyQualifiedPath
      val subnodeRef = new core.node.Builder.Node(new names.mutable.Supply(subpath), subpath)
      val subbuilder = new Builder(subnodeRef)
      val inv = new Invocation(superbuilder = this, instance = instance, builder = subbuilder)
      val node = f(inv)
      nested.subnode(instance.name, subnodeRef, inv.arguments.toList)
      node

    def invoke[T <: Node : ClassTag](f: Invocation => T)(using location: lack.meta.macros.Location): T =
      val name = location.enclosing.getOrElse(
          summon[ClassTag[T]].runtimeClass.getSimpleName())
      invokeWithName(name)(f)

  class Invocation(val superbuilder: Builder, val instance: names.Ref, val builder: Builder):
    val arguments: mutable.ArrayBuffer[core.term.Exp] = mutable.ArrayBuffer()

    // TODO keep track of meta-level arguments
    def typearg[T: SortRepr](name: String): Unit = {}
    def metaarg(name: String, v: Integer): Unit = {}

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
     * >    new SoFar(invocation.arg("e", e))
     * >  }
     *
     * This requires some extra boilerplate for each node definition. In the future
     * it should be relatively straightforward to have a macro generate these invocations
     * from the class constructor.
     */
    def arg[T](name: String, argvalue: Stream[T])(using location: lack.meta.macros.Location): Stream[T] =
      val v = builder.nodeRef.fresh(
        names.ComponentSymbol.fromScalaSymbol(name),
        core.node.Variable(argvalue.sort, location, core.node.Variable.Argument))
      arguments += argvalue._exp
      new Stream[T](v)(using argvalue.sortRepr)
