package lack.meta.source

import lack.meta.base.Integer
import lack.meta.core
import lack.meta.source.stream.{Stream, SortRepr}

import scala.collection.mutable
import scala.reflect.ClassTag

object node:
  class Builder(val nodeRef: core.builder.Node):
    var nested = nodeRef.nested

    def memo1[T](it: Stream[T])(f: core.term.Exp => core.term.Exp)(using location: lack.meta.macros.Location): Stream[T] =
      val e   = it._exp
      val mem = nested.memo(f(e), it.sort)
      new Stream(mem)(using it.sortRepr)

    def memo2[T](a: Stream[T], b: Stream[T])(f: (core.term.Exp, core.term.Exp) => core.term.Exp)(using location: lack.meta.macros.Location): Stream[T] =
      val mem = nested.memo(f(a._exp, b._exp), a.sort)
      new Stream(mem)(using a.sortRepr)

    def memo2x1[T, U, V: SortRepr]
      (a: Stream[T], b: Stream[U])
      (f: (core.term.Exp, core.term.Exp) => core.term.Exp)
      (using location: lack.meta.macros.Location): Stream[V] =
      val sort = summon[SortRepr[V]].sort
      val mem = nested.memo(f(a._exp, b._exp), sort)
      new Stream(mem)

    def memo3x1[T, U, V, W: SortRepr]
      (a: Stream[T], b: Stream[U], c: Stream[V])
      (f: (core.term.Exp, core.term.Exp, core.term.Exp) => core.term.Exp)
      (using location: lack.meta.macros.Location): Stream[W] =
      val sort = summon[SortRepr[W]].sort
      val mem = nested.memo(f(a._exp, b._exp, c._exp), sort)
      new Stream(mem)

    /** Call a subnode.
     * Invoking subnodes requires a little bit of indirection, because we want to
     * keep a clear interface between the calling node and the called node.
     * ...
     */
    def invokeWithName[T <: Node](name: String)(f: NodeInvocation => T): T =
      val instance = nodeRef.freshSubnodeRef(core.names.ComponentSymbol.fromScalaSymbol(name))
      val subpath = instance.path :+ instance.name
      val subnodeRef = new core.builder.Node(new core.builder.Supply(subpath), subpath)
      val subbuilder = new Builder(subnodeRef)
      val inv = new NodeInvocation(superbuilder = this, instance = instance, builder = subbuilder)
      val node = f(inv)
      nested.subnode(instance.name, subnodeRef, inv.arguments.toList)
      node

    def invoke[T <: Node : ClassTag](f: NodeInvocation => T)(using location: lack.meta.macros.Location): T =
      val name = location.enclosing.getOrElse(
          summon[ClassTag[T]].runtimeClass.getSimpleName())
      invokeWithName(name)(f)

  class NodeInvocation(val superbuilder: Builder, val instance: core.names.Ref, val builder: Builder):
    val arguments: mutable.ArrayBuffer[core.term.Exp] = mutable.ArrayBuffer()

    // TODO keep track of meta-level arguments
    def typearg[T: SortRepr](name: String): Unit = {}
    def metaarg(name: String, v: Integer): Unit = {}

    /** Mark an expression as an argument to a subnode.
     *
     * If you have a node you want to call which looks something like:
     * > class Always(e: Stream[Bool]) extends Node
     * then you might try to call it from another node as:
     * > Always(x > 5)
     *
     * However, the problem with the above call is that the subnode gets directly
     * instantiated with any occurrences of e replaced with the value `x > 5`,
     * losing the fact that e referred to the first parameter. This substitution
     * makes it hard to do modular proofs: if Always has some local propositions
     * that we'd like to prove, but all we have is a few different instances of
     * Always with different arguments, then it becomes hard to know which parts
     * of the proof can be reused across the different instances.
     * Copilot has a similar problem with this "eager substitution", which is why
     * they don't support contracts for modular proofs.
     *
     * We get around this by requiring the invocation to explicitly mark the
     * parameters that will be substituted for argument values. We bundle this up
     * inside a "NodeInvocation" object which is passed to the Node base class
     * like so:
     * > class Always(e: Stream[Bool], invocation: NodeInvocation) extends Node(invocation)
     *
     * Then, you can call it by calling builder.invoke:
     * > def always(e: Stream[Bool])(using builder: Builder): Always =
     * >  builder.invoke { invocation =>
     * >    new Always(invocation.arg("e", e))
     * >  }
     *
     * This requires some extra boilerplate for each node definition. In the future
     * it should be relatively straightforward to have a macro generate these invocations
     * from the class constructor.
     */
    def arg[T](name: String, argvalue: Stream[T])(using location: lack.meta.macros.Location): Stream[T] =
      val v = builder.nodeRef.fresh(
        core.names.ComponentSymbol.fromScalaSymbol(name),
        core.builder.Variable(argvalue.sort, location, core.builder.Variable.Argument))
      arguments += argvalue._exp
      new Stream[T](v)(using argvalue.sortRepr)




  case class Activate(reset: Stream[stream.Bool] = Activate.falses, when: Stream[stream.Bool] = Activate.trues)
  object Activate:
    val trues: Stream[stream.Bool]  =
      new Stream(core.term.Exp.Val(core.term.Val.Bool(true)))
    val falses: Stream[stream.Bool] =
      new Stream(core.term.Exp.Val(core.term.Val.Bool(false)))
    val always = Activate(reset = falses, when = trues)

  // case class NodeApplication(activate: Activate, superbuilder: Builder)

  // TODO: node instantiation should force bindings for arguments with builder.nodeRef.memoForce.
  // Arguments need to be treated as special bindings on node so that we can re-abstract them
  // after they've been instantiated (for C code generation, and for contracts).
  // Requires some re-jigging so that the caller can construct the builder first,
  // add the arguments and get fresh names for them, and then instantiate the node subclass
  abstract class Node(invocation: NodeInvocation):

    given builder: Builder = invocation.builder

    inline given location: lack.meta.macros.Location = lack.meta.macros.location

    protected class Lhs[T: SortRepr](_exp: core.term.Exp) extends Stream[T](_exp):
      def v: core.names.Component = _exp match
        case core.term.Exp.Var(v, _) =>
          require(v.path == builder.nodeRef.path)
          v.name
        case _ =>
          assert(false, s"Internal error: bad Lhs[T]: ${_exp} should be a bare variable")


    protected def declare[T: SortRepr](name: String, mode: core.builder.Variable.Mode)(using loc: lack.meta.macros.Location): Lhs[T] =
      val sort = summon[SortRepr[T]].sort
      val v = core.builder.Variable(sort, loc, mode)
      new Lhs(builder.nodeRef.fresh(lack.meta.core.names.ComponentSymbol.fromScalaSymbol(name), v))

    protected def local[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath, core.builder.Variable.Local)

    protected def output[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath, core.builder.Variable.Output)

    protected def property(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Property))

    protected def requires(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Require))

    protected def guarantees(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Guarantee))

    protected def sorry(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Sorry))

    protected def bind[T](lhs: Lhs[T], rhs: Stream[T]) =
      builder.nested.equation(lhs.v, rhs._exp)

    extension [T](lhs: Lhs[T])
      protected def := (rhs: Stream[T]) =
        bind(lhs, rhs)

    extension [T: SortRepr, U: SortRepr](lhs: (Lhs[T], Lhs[U]))
      protected def := (rhs: Stream[(T, U)]) =
        bind(lhs._1, rhs._1)
        bind(lhs._2, rhs._2)

    protected abstract class Nested(activate: Activate = Activate.always) extends reflect.Selectable:
      given builder: Builder = new Builder(invocation.builder.nodeRef)
      val w = builder.nested.nested(core.builder.Selector.When(activate.when._exp))
      val r = w.nested(core.builder.Selector.Reset(activate.reset._exp))
      builder.nested = r
