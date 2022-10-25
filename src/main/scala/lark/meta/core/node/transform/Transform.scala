package lark.meta.core.node.transform

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.collection.{Graph, MultiMap}

import scala.collection.{mutable, immutable}
import lark.meta.core.node.{Node, Variable, Schedule}
import lark.meta.core.node.Node.Binding
import lark.meta.core.term.{Exp, Flow}
import lark.meta.core.term.Compound

object Transform:
  /** Inline the local bindings in nodes. */
  def map(nodes: Iterable[Node])(body: Node => Node): Iterable[Node] =
    val map = scala.collection.mutable.SortedMap[names.Ref, Node]()
    nodes.map { n =>
      val nX  = body(n)
      val nXX = nX.copy(subnodes = nX.subnodes.map { (k,v) =>
        k -> map(v.klass)
      })
      map += (n.klass -> nXX)
      nXX
    }
