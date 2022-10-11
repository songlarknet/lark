package lack.meta.driver

import lack.meta.core
import lack.meta.source.Node
import lack.meta.source.node.{Base, Builder, Invocation, Sugar}
import scala.reflect.ClassTag

object Invoke:
  def topnodes[T <: Base: ClassTag](body: Invocation => T): List[core.node.Builder.Node] =
    val top = core.node.Builder.Node.top()
    given builder: Builder = new Builder(top)
    val sn = Sugar.subnode(builder)(body)
    top.subnodes.values.toList

  def allNodes[T <: Base: ClassTag](body: Invocation => T): List[core.node.Builder.Node] =
    topnodes(body).flatMap(_.allNodes)
