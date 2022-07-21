package lack.meta.core

import lack.meta.base.Integer
import lack.meta.core.sort.Sort
import lack.meta.core.term.{Exp, Prim, Var, Val}
import lack.meta.core.prop.{Form, Judgment}

object builder:
  class Supply:
    var ixes: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map[String, Int]().withDefaultValue(0)
    def fresh(prefix: String, sort: Sort): Var =
      val ix = ixes(prefix)
      ixes(prefix) += 1
      Var(prefix, ix, sort)

    // TODO: add map from Var to Node where it's defined?
    // TODO: top-level wants a list of all the types used, eg structs

  object Node:
    def top(): Node = new Node(new Supply, "<top>", Exp.Val(Val.Bool(false)), Exp.Val(Val.Bool(true)))

  class Node(val supply: Supply, val name: String, val reset: Exp, val when: Exp):
    // TODO add List[Var] for declaring args, or change vars to List[(Var, Arg | Local | State | Output)]
    var subnodes: List[Node] = List()
    var bindings: List[(Exp, Exp)] = List()
    var props: List[Judgment] = List()
    var vars: List[Var] = List()

    def allProps: List[Judgment] = props ++ subnodes.flatMap(_.allProps)
    def allPropObligations: List[Judgment] = allProps.filter(p => p.form == Form.Property)

    def fresh(prefix: String, sort: Sort): Var =
      val v = supply.fresh(prefix, sort)
      vars = v :: vars
      v

    def subnode(name: String, reset: Exp, when: Exp): Node =
      val c = new Node(supply, name, reset, when)
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
      case Exp.Var(_) => rhs
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
      val v = Exp.Var(fresh("", sort))
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

      s"""Node: ${name}
         |  Reset: ${reset.pretty}; When: ${when.pretty}
         |${indent("Bindings:", bindings.map(x => s"${x._1.pretty} := ${x._2.pretty}"))}
         |${indent("Subnodes:", subnodes.map(x => x.pretty))}
         |${indent("Props:", props.map(x => x.pretty))}
         |""".stripMargin

