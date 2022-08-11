package lack.meta.core

import lack.meta.base.Integer
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Val}
import lack.meta.core.prop.{Form, Judgment}
import javax.naming.Binding

object builder:
  /** Node-level context with a fresh name supply */
  class Supply(val path: List[names.Component]):
    var ixes: scala.collection.mutable.Map[names.ComponentSymbol, Int] = scala.collection.mutable.Map[names.ComponentSymbol, Int]().withDefaultValue(0)

    def fresh(name: names.ComponentSymbol): names.Ref =
      val ix = ixes(name)
      ixes(name) += 1
      names.Ref(path, names.Component(name, ix))

    def fresh(name: names.ComponentSymbol, sort: Sort): Exp.Var =
      Exp.Var(fresh(name), sort)

    // TODO: want a second sort of context that's program-level
    // TODO: add map from Var to Node where it's defined?
    // TODO: top-level wants a list of all the types used, eg structs
    // var nodes: List[Node] = List()
    // var sorts: List[Sort] = List()

  object Node:
    def top(): Node = new Node(new Supply(List()), List(), Exp.Val(Val.Bool(false)), Exp.Val(Val.Bool(true)))

  // object flow:
  //   sealed trait Bind
  //   case class Context(flag: Var, when: Exp, reset: Exp, binds: List[Bind]) extends Bind
  //   case class Instance(vars: List[Var], node: Node, args: List[Exp]) extends Bind
  //   case class Binding(lhs: Var, rhs: Exp) extends Bind

  class Node(val supply: Supply, val path: List[names.Component], val reset: Exp, val when: Exp):
    // TODO: add List[Var] for declaring args, or change vars to List[(Var, Arg | Local | State | Output)]
    // TODO: distinguish between nodes and node instances.
    var subnodes: List[Node]       = List()
    var bindings: List[(Exp, Exp)] = List()
    var props:    List[Judgment]   = List()
    var vars:     List[Exp.Var]    = List()

    def allProps: List[Judgment] = props ++ subnodes.flatMap(_.allProps)
    /** All obligations we need to prove. TODO: restructure, deal with contracts */
    def allPropObligations: List[Judgment] = allProps.filter(p => p.form == Form.Property)

    def fresh(prefix: names.ComponentSymbol, sort: Sort): Exp.Var =
      val v = supply.fresh(prefix, sort)
      vars = v :: vars
      v

    def subnode(name: names.ComponentSymbol, reset: Exp, when: Exp): Node =
      val inst = supply.fresh(name)
      val s = new Supply(supply.path :+ inst.name)
      val c = new Node(s, s.path, reset, when)
      subnodes = c :: subnodes
      c

    def bind(lhs: Exp, rhs: Exp): Unit =
      bindings = (lhs -> rhs) :: bindings

    /** Create a new binding for the given expression.
     *
     * @param rhs
     * @param sort
     * */
    def memo(rhs: Exp, sort: Sort): Exp = rhs match
      case Exp.Var(_, _) => rhs
      case Exp.Val(_) => rhs
      case _ =>
        // Try to re-use
        bindings.find { case (v,rhsx) => rhs == rhsx } match
          case None =>
            memoForce(rhs, sort)
          case Some((v,rhsx)) =>
            v

    /** Create a new binding for the given expression, even for simple expressions.
     * This creates bindings for simple expressions such as variables and values;
     * doesn't reuse existing bindings.
     */
    def memoForce(rhs: Exp, sort: Sort): Exp =
      val v = fresh(names.ComponentSymbol.EMPTY, sort)
      bind(v, rhs)
      v

    def prop(j: Judgment): Unit =
      props = j :: props

    def pretty: String =
      def indent(head: String, xs: List[String]): String = xs match
        case List() => ""
        case _ :: _ =>
          val xss = xs.flatMap(x => x.split("\n"))
          s"  $head\n" + xss.map(x => s"    $x").mkString("\n")

      s"""Node: ${path.map(_.pretty).mkString(".")}
         |  Reset: ${reset.pretty}; When: ${when.pretty}
         |${indent("Bindings:", bindings.map(x => s"${x._1.pretty} := ${x._2.pretty}"))}
         |${indent("Subnodes:", subnodes.map(x => x.pretty))}
         |${indent("Props:", props.map(x => x.pretty))}
         |""".stripMargin

