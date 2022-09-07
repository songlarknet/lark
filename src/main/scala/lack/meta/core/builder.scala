package lack.meta.core

import lack.meta.macros.Location
import lack.meta.base.num.Integer
import lack.meta.base.names
import lack.meta.base.pretty.indent
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}
import lack.meta.core.prop.{Form, Judgment}

import scala.collection.mutable

/** Mutable builder for node-based transition systems. */
object builder:
  /** Node-level context with a fresh name supply */
  class Supply(val path: List[names.Component]):
    var ixes: mutable.Map[names.ComponentSymbol, Int] = mutable.Map().withDefaultValue(0)

    def freshRef(name: names.ComponentSymbol, forceIndex: Boolean = false): names.Ref =
      val ix = ixes(name)
      val ixy = if (ix > 0 || forceIndex) Some(ix) else None
      ixes(name) += 1
      names.Ref(path, names.Component(name, ixy))

    def freshInit(): names.Ref =
      freshRef(names.ComponentSymbol.INIT, forceIndex = true)

    // TODO: want a second sort of context that's program-level
    // TODO: add map from Var to Node where it's defined?
    // TODO: top-level wants a list of all the types used, eg structs
    // var nodes: List[Node] = List()
    // var sorts: List[Sort] = List()

  /** Binding contexts, called "context" in core.md. */
  sealed trait Binding:
    def pretty: String
  object Binding:
    case class Equation(lhs: names.Component, rhs: Exp) extends Binding:
      def pretty = s"${lhs.pretty} = ${rhs.pretty}"
    case class Subnode(subnode: names.Component, args: List[Exp]) extends Binding:
      def pretty = s"Subnode ${subnode.pretty}(${args.map(_.pretty).mkString(", ")})"
    class Nested(val init: names.Component, val selector: Selector, val node: Node) extends Binding:
      val children: mutable.ArrayBuffer[Binding] = mutable.ArrayBuffer()

      def pretty: String =
        s"${selector.pretty} @init(${init.pretty}):\n" +
        indent(children.map(_.pretty).toList)

      // TODO do merging / cse on append?
      def append(b: Binding): Unit =
        children += b

      def nested(selector: Selector): Nested =
        val i = node.supply.freshInit()
        val n = new Nested(i.name, selector, node)
        append(n)
        n


      /** Create a new binding for the given expression.
       *
       * @param rhs
       * @param sort
       * */
      def memo(rhs: Exp)(using location: Location): Exp = rhs match
        case Exp.Var(_, _) => rhs
        case Exp.Val(_, _) => rhs
        case _ =>
          // Try to re-use binding if we already have one.
          //
          // TODO: apply some local rewrites, eg "v -> pre e = Fby(v, e)"
          // and const prop
          // TODO: look in other bindings.
          // TODO: UNSOUND: do not reuse bindings that call undefined
          //
          // Maybe we want this to be as dumb as possible so that the
          // source translation is "obviously correct".
          // Then we can do better CSE in later stages.
          children.flatMap {
            case Equation(lhs, rhsx) if rhs == rhsx =>
              val v = node.vars(lhs)
              assert(v.sort == rhs.sort,
                s"""When trying to reuse existing binding
                  ${lhs} : ${v.sort} = ${rhsx}
                for requested expression ${rhs} : ${sort} at location ${location},
                the two sorts don't match.
                """)
              Seq(node.xvar(lhs))
            case _ => Seq.empty
          }.headOption.getOrElse(memoForce(rhs))

      /** Create a new binding for the given expression, even for simple expressions.
       * This creates bindings for simple expressions such as variables and values;
       * doesn't reuse existing bindings.
       */
      def memoForce(rhs: Exp)(using location: Location): Exp =
        val vv = Variable(rhs.sort, location, Variable.Generated)
        val name = location.enclosing.fold(names.ComponentSymbol.LOCAL)(i => names.ComponentSymbol.fromScalaSymbol(i))
        val v = node.fresh(name, vv, forceIndex = true)
        append(Equation(v.v.name, rhs))
        v

      def equation(lhs: names.Component, rhs: Exp): Unit =
        append(Equation(lhs, rhs))

      def subnode(name: names.Component, subnode: Node, args: List[Exp]): Unit =
        assert(!node.vars.contains(name), s"tried to allocate a subnode named ${name} but that name is already used by variable ${node.vars(name)}")
        assert(!node.subnodes.contains(name), s"tried to allocate a subnode named ${name} but that name is already used by subnode ${node.subnodes(name)}")
        node.subnodes += name -> subnode
        append(Subnode(name, args))


  sealed trait Selector:
    def pretty: String
  object Selector:
    case class When(clock: Exp) extends Selector:
      def pretty: String = s"When(${clock.pretty})"
    case class Reset(clock: Exp) extends Selector:
      def pretty: String = s"Reset(${clock.pretty})"

  object Node:
    def top(): Node = new Node(new Supply(List()), List())

  object Variable:
    sealed trait Mode
    case object Argument extends Mode
    case object Local extends Mode
    case object Output extends Mode
    case object Generated extends Mode

  case class Variable(sort: Sort, location: Location, mode: Variable.Mode)

  class Node(val supply: Supply, val path: List[names.Component]):
    val params:   mutable.ArrayBuffer[names.Component]   = mutable.ArrayBuffer()
    var vars:     mutable.Map[names.Component, Variable] = mutable.Map()
    // TODO subnodes need location information
    var subnodes: mutable.Map[names.Component, Node]     = mutable.Map()
    var props:    mutable.ArrayBuffer[Judgment]          = mutable.ArrayBuffer()

    var nested: Binding.Nested = new Binding.Nested(supply.freshInit().name, Selector.When(term.Exp.Val(Sort.Bool, term.Val.Bool(true))), this)

    def allProps: Iterable[Judgment] = props ++ subnodes.values.flatMap(_.allProps)
    /** All obligations we need to prove. TODO: restructure, deal with contracts */
    def allPropObligations: Iterable[Judgment] = allProps.filter(p => p.form == Form.Property)

    /** All dependent nodes in the system, including this node */
    def allNodes: Iterable[Node] =
      val subs = subnodes.values.flatMap(_.allNodes)
      // TODO: filter out non-unique nodes
      subs ++ Seq(this)

    def fresh(name: names.ComponentSymbol, variable: Variable, forceIndex: Boolean = false): Exp.Var =
      val r = supply.freshRef(name, forceIndex)
      val v = Exp.Var(variable.sort, r)
      vars += r.name -> variable
      if (variable.mode == Variable.Argument)
        params += r.name
      v

    def freshSubnodeRef(name: names.ComponentSymbol): names.Ref =
      supply.freshRef(name) // , forceIndex = true)

    def xvar(name: names.Component): Exp.Var =
      val v = vars(name)
      Exp.Var(v.sort, names.Ref(path, name))


    def prop(j: Judgment): Unit =
      props += j

    def pretty: String =
      val paramsP = params.map(p => s"${p.pretty} : ${xvar(p).sort.pretty}")
      s"""Node ${path.map(_.pretty).mkString(".")}(${paramsP.mkString(", ")})
         |${indent("Vars:", vars.map(x => s"${x._2.mode} ${x._1.pretty} : ${x._2.sort}${x._2.location.pretty}").toList)}
         |${indent("Bindings:", nested.children.map(x => x.pretty).toList)}
         |${indent("Subnodes:", subnodes.map(x => s"${x._1.pretty} = ${x._2.pretty}").toList)}
         |${indent("Props:", props.map(x => x.pretty).toList)}
         |""".stripMargin

