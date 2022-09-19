package lack.meta.source

import lack.meta.base.num.Integer
import lack.meta.base.names
import lack.meta.core
import lack.meta.source.stream.{Stream, SortRepr}

import scala.collection.mutable
import scala.reflect.ClassTag

object node:
  class Builder(val nodeRef: core.builder.Node, nestedO: Option[core.builder.Nested] = None):
    var nested = nestedO.getOrElse(nodeRef.nested)

    def withNesting[T](neu: core.builder.Nested)(f: => T): T =
      val old = nested
      try {
        nested = neu
        f
      } finally {
        nested = old
      }

    def activate(activate: Activate, parent: core.builder.Nested = nested): core.builder.Nested =
      val w = parent.merge().when(activate.when._exp)
      val r = w.reset(activate.reset._exp)
      r

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
    def invokeWithName[T <: Node](name: String)(f: NodeInvocation => T): T =
      val instance = nodeRef.freshSubnodeRef(names.ComponentSymbol.fromScalaSymbol(name))
      val subpath = instance.fullyQualifiedPath
      val subnodeRef = new core.builder.Node(new names.mutable.Supply(subpath), subpath)
      val subbuilder = new Builder(subnodeRef)
      val inv = new NodeInvocation(superbuilder = this, instance = instance, builder = subbuilder)
      val node = f(inv)
      nested.subnode(instance.name, subnodeRef, inv.arguments.toList)
      node

    def invoke[T <: Node : ClassTag](f: NodeInvocation => T)(using location: lack.meta.macros.Location): T =
      val name = location.enclosing.getOrElse(
          summon[ClassTag[T]].runtimeClass.getSimpleName())
      invokeWithName(name)(f)

  class NodeInvocation(val superbuilder: Builder, val instance: names.Ref, val builder: Builder):
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
     * inside a "NodeInvocation" object which is passed to the Node base class
     * like so:
     * > class SoFar(e: Stream[Bool], invocation: NodeInvocation) extends Node(invocation)
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
        core.builder.Variable(argvalue.sort, location, core.builder.Variable.Argument))
      arguments += argvalue._exp
      new Stream[T](v)(using argvalue.sortRepr)




  case class Activate(reset: Stream[stream.Bool] = Activate.falses, when: Stream[stream.Bool] = Activate.trues)
  object Activate:
    val trues: Stream[stream.Bool]  =
      new Stream(core.term.Exp.Val(core.sort.Sort.Bool, core.term.Val.Bool(true)))
    val falses: Stream[stream.Bool] =
      new Stream(core.term.Exp.Val(core.sort.Sort.Bool, core.term.Val.Bool(false)))
    val always = Activate(reset = falses, when = trues)

  abstract class Node(invocation: NodeInvocation):

    given builder: Builder = invocation.builder

    inline given location: lack.meta.macros.Location = lack.meta.macros.location

    protected class Lhs[T: SortRepr](_exp: core.term.Exp) extends Stream[T](_exp):
      def v: names.Component = _exp match
        case core.term.Exp.Var(_, v) =>
          require(v.prefix == builder.nodeRef.path)
          v.name
        case _ =>
          assert(false, s"Internal error: bad Lhs[T]: ${_exp} should be a bare variable")


    protected def declare[T: SortRepr](name: String, mode: core.builder.Variable.Mode)(using loc: lack.meta.macros.Location): Lhs[T] =
      val sort = summon[SortRepr[T]].sort
      val v = core.builder.Variable(sort, loc, mode)
      new Lhs(builder.nodeRef.fresh(names.ComponentSymbol.fromScalaSymbol(name), v))

    protected def local[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath, core.builder.Variable.Local)

    protected def output[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath, core.builder.Variable.Output)

    protected def bindProperty(syntax: core.prop.Syntax, name: String)(prop: Stream[stream.Bool])(using loc: lack.meta.macros.Location) =
      val locx = loc <> builder.nodeRef.locate(prop._exp)
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, syntax, locx))

    protected def check(name: String)(prop: Stream[stream.Bool])(using loc: lack.meta.macros.Location) =
      bindProperty(core.prop.Syntax.Check, name)(prop)

    protected def requires(name: String)(prop: Stream[stream.Bool])(using loc: lack.meta.macros.Location) =
      bindProperty(core.prop.Syntax.Require, name)(prop)

    protected def guarantees(name: String)(prop: Stream[stream.Bool])(using loc: lack.meta.macros.Location) =
      bindProperty(core.prop.Syntax.Guarantee, name)(prop)

    protected def sorry(name: String)(prop: Stream[stream.Bool])(using loc: lack.meta.macros.Location) =
      bindProperty(core.prop.Syntax.Sorry, name)(prop)

    protected def bind[T](lhs: Lhs[T], rhs: Stream[T])(using builder: Builder) =
      builder.nested.equation(lhs.v, core.term.Flow.Pure(rhs._exp))

    extension [T](lhs: Lhs[T])
      protected def := (rhs: Stream[T])(using builder: Builder) =
        bind(lhs, rhs)

    extension [T: SortRepr, U: SortRepr](lhs: (Lhs[T], Lhs[U]))
      protected def := (rhs: Stream[(T, U)])(using builder: Builder) =
        bind(lhs._1, rhs._1)
        bind(lhs._2, rhs._2)

    protected abstract class Nested(activate: Activate = Activate.always) extends reflect.Selectable:
      given builder: Builder = new Builder(
        invocation.builder.nodeRef,
        Some(invocation.builder.activate(activate)))

    protected abstract class Merge(using builder: Builder) extends reflect.Selectable:
      private val merge = builder.nested.merge()

      abstract class When(when: Stream[stream.Bool], reset: Stream[stream.Bool] = Activate.falses) extends reflect.Selectable:
        given builder: Builder = new Builder(
          Merge.this.builder.nodeRef,
          Some(merge.when(when._exp).reset(reset._exp)))

    protected abstract class Reset(reset: Stream[stream.Bool])(using superbuilder: Builder) extends reflect.Selectable:
      given builder: Builder = new Builder(
        superbuilder.nodeRef,
        Some(superbuilder.nested.reset(reset._exp)))
