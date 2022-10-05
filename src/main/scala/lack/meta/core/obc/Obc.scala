package lack.meta.core.obc

import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.core.{Prop, Sort}
import lack.meta.core.term.Exp

import scala.collection.immutable.SortedMap

/** Obc is a minimal object-based language. Programs are translated from the
 * core.node.Node representation into Obc before being translated to a
 * target language such as C or Scala.
 */
object Obc:

  /** Imperative statements */
  sealed trait Statement extends pretty.Pretty:
    def <>(that: Statement): Statement = (this, that) match
      case (Statement.Skip, _) => that
      case (_, Statement.Skip) => this
      case (Statement.Seq(s1, s2), _) => Statement.Seq(s1, s2 <> that)
      case (Statement.Ite(p, t, f), Statement.Ite(px, tx, fx))
        if p == px =>
          Statement.Ite(p, t <> tx, f <> fx)
      case _ => Statement.Seq(this, that)

  object Statement:

    /** Assignment to local variable */
    case class Assign(name: names.Component, exp: Exp) extends Statement:
      def ppr = name.ppr <+> pretty.gets <+> pretty.nest(exp.ppr)

    /** Assignment to field in self object (self.name := exp) */
    case class AssignSelf(name: names.Component, exp: Exp) extends Statement:
      def ppr = pretty.text("self.") <> name.ppr <+> pretty.gets <+> pretty.nest(exp.ppr)

    /** If-then-else */
    case class Ite(p: Exp, t: Statement, f: Statement) extends Statement:
      def ppr =
        pretty.text("if") <+> pretty.nest(p.ppr) <+> pretty.text("then") <@>
          pretty.indent(t.ppr) <@>
        (f match
          case Skip => pretty.emptyDoc
          case Ite(_, _, _) => pretty.text("else") <+> f.ppr
          case _ => pretty.text("else") <@>
            pretty.indent(f.ppr))

    def ite(p: Exp, t: Statement, f: Statement): Statement = (t, f) match
      case (Skip, Skip) => Skip
      case _ => Ite(p, t, f)

    /** Sequential composition (semicolon) */
    case class Seq(s: Statement, t: Statement) extends Statement:
      def ppr = s.ppr <@> t.ppr

    /** Empty statement */
    case object Skip extends Statement:
      def ppr = "skip"

    /** Method call on a sub-object of the current instance.
     * The assigns list can refer to local or return variables in the current
     * method. Instance refers to an object instance in the current class.
     * The method implementation is statically determined by the type of the
     * object instance.
     */
    case class Call(assigns: List[names.Component], klass: names.Ref, method: names.Component, instance: names.Component, args: List[Exp]) extends Statement:
      def ppr =
        pretty.tupleP(assigns) <+> pretty.gets <+>
          klass.ppr <> pretty.text("::") <> method.ppr <>
          pretty.tupleP(instance :: args)


    def concat(is: List[Statement]): Statement =
      is.fold(Skip)(_ <> _)

  final case class Method(
    name:    names.Component,
    params:  List[Sort.Sorted],
    returns: List[Sort.Sorted],
    locals:  List[Sort.Sorted],
    body:    Statement,
  ) extends pretty.Pretty:
    def ppr =
      pretty.text("method ") <+> name.ppr <> pretty.tupleP(params) <@>
      pretty.text("returns") <+> pretty.tupleP(returns) <@>
      pretty.text("locals ") <+> pretty.tupleP(locals) <> pretty.colon <@>
      pretty.indent(body.ppr)

    val paramsMap  = SortedMap.from(params.map(_.tuple))
    val returnsMap = SortedMap.from(returns.map(_.tuple))
    val localsMap  = SortedMap.from(locals.map(_.tuple))

  object Method:
    val reset: names.Component =
      names.Component(names.ComponentSymbol.fromScalaSymbol("reset"))
    val step: names.Component =
      names.Component(names.ComponentSymbol.fromScalaSymbol("step"))

  final case class Class(
    name:    names.Ref,
    fields:  List[Sort.Sorted],
    objects: List[(names.Component, names.Ref)],
    methods: List[Method],
    props:   List[Prop.Judgment],
  ) extends pretty.Pretty:
    def ppr =
      pretty.text("class   ") <+> name.ppr <@>
      pretty.text("fields  ") <+> pretty.tupleP(fields) <@>
      pretty.text("objects ") <+> pretty.tuple(objects.map { case (k,v) => k.ppr <> pretty.colon <+> v.ppr}.toSeq) <> pretty.colon <@>
      pretty.indent(pretty.vsep(methods.map(_.ppr)))

    val fieldsMap  = SortedMap.from(fields.map(_.tuple))
    val objectsMap = SortedMap.from(objects)
    val methodsMap = SortedMap.from(methods.map(m => (m.name, m)))

  object Class:
    def self: names.Prefix = names.Prefix(List(names.Component(names.ComponentSymbol.fromScalaSymbol("self"))))