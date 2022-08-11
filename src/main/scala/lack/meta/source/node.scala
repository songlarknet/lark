package lack.meta.source

import lack.meta.core
import lack.meta.source.stream.{Stream, SortRepr}

object node:
  class Builder(val nodeRef: core.builder.Node):
    def memo1[T](it: Stream[T])(f: core.term.Exp => core.term.Exp): Stream[T] =
      val e   = it._exp
      val mem = nodeRef.memo(f(e), it.sort)
      new Stream(mem)(using it.sortRepr)

    def memo2[T](a: Stream[T], b: Stream[T])(f: (core.term.Exp, core.term.Exp) => core.term.Exp): Stream[T] =
      val mem = nodeRef.memo(f(a._exp, b._exp), a.sort)
      new Stream(mem)(using a.sortRepr)

    def memo2x1[T, U, V: SortRepr]
      (a: Stream[T], b: Stream[U])
      (f: (core.term.Exp, core.term.Exp) => core.term.Exp): Stream[V] =
      val sort = summon[SortRepr[V]].sort
      val mem = nodeRef.memo(f(a._exp, b._exp), sort)
      new Stream(mem)

    def memo3x1[T, U, V, W: SortRepr]
      (a: Stream[T], b: Stream[U], c: Stream[V])
      (f: (core.term.Exp, core.term.Exp, core.term.Exp) => core.term.Exp): Stream[W] =
      val sort = summon[SortRepr[W]].sort
      val mem = nodeRef.memo(f(a._exp, b._exp, c._exp), sort)
      new Stream(mem)

  case class Activate(reset: Stream[stream.Bool], when: Stream[stream.Bool])
  object Activate:
    val trues: Stream[stream.Bool]  =
      new Stream(core.term.Exp.Val(core.term.Val.Bool(true)))
    val falses: Stream[stream.Bool] =
      new Stream(core.term.Exp.Val(core.term.Val.Bool(false)))
    val always = Activate(reset = falses, when = trues)

  case class NodeApplication(activate: Activate, superbuilder: Builder)

  // TODO: node instantiation should force bindings for arguments with builder.nodeRef.memoForce.
  // Arguments need to be treated as special bindings on node so that we can re-abstract them
  // after they've been instantiated (for C code generation, and for contracts).
  // Requires some re-jigging so that the caller can construct the builder first,
  // add the arguments and get fresh names for them, and then instantiate the node subclass
  abstract class Node(application: NodeApplication):
    protected val superbuilder = application.superbuilder
    protected val activate     = application.activate

    given builder: Builder =
      new Builder(superbuilder.nodeRef.subnode(
        lack.meta.core.names.ComponentSymbol.fromScalaSymbol(this.getClass().getSimpleName()),
        activate.reset._exp,
        activate.when._exp))

    inline given location: lack.meta.macros.Location = lack.meta.macros.location

    protected class Lhs[T: SortRepr](_exp: core.term.Exp) extends Stream[T](_exp)


    protected def declare[T: SortRepr](name: String): Lhs[T] =
      new Lhs(builder.nodeRef.fresh(lack.meta.core.names.ComponentSymbol.fromScalaSymbol(name), summon[SortRepr[T]].sort))

    protected def local[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath)

    protected def output[T: SortRepr](using loc: lack.meta.macros.Location): Lhs[T] =
      declare(loc.prettyPath)

    protected def property(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Property))

    protected def requires(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Require))

    protected def guarantees(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Guarantee))

    protected def sorry(name: String)(prop: Stream[stream.Bool]) =
      builder.nodeRef.prop(core.prop.Judgment(name, prop._exp, core.prop.Form.Sorry))

    protected def bind[T](lhs: Lhs[T], rhs: Stream[T]) =
      builder.nodeRef.bind(lhs._exp, rhs._exp)

    extension [T](lhs: Lhs[T])
      protected def := (rhs: Stream[T]) =
        bind(lhs, rhs)

    extension [T: SortRepr, U: SortRepr](lhs: (Lhs[T], Lhs[U]))
      protected def := (rhs: Stream[(T, U)]) =
        bind(lhs._1, rhs._1)
        bind(lhs._2, rhs._2)

