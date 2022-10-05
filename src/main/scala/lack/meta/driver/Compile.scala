package lack.meta.driver

import lack.meta.base.names
import lack.meta.base.names.given
import lack.meta.base.pretty
import lack.meta.core
import lack.meta.core.node.Schedule

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8}
import lack.meta.source.Node
import lack.meta.source.Node.{Builder}

import scala.collection.immutable.SortedMap

/** Compile a program to executable code. */
object Compile:
  def compile()(f: Node.Invocation => Node): Unit =
    val top = lack.meta.core.node.Builder.Node.top()
    given builder: Builder = new Builder(top)
    builder.invoke(f)
    val subnodes = builder.nodeRef.allNodes.filter(_ != top)
    val frozen = subnodes.map(_.freeze)
    val scheds = schedules(frozen)
    val obcs = core.obc.FromNode.program(frozen, scheds)

    core.obc.Check.program(obcs, core.obc.Check.Options())

    val opts = core.target.C.Options(basename = "lack", classes = obcs)
    val doc  = core.target.C.header(opts)
    val src  = core.target.C.source(opts)
    println(pretty.layout(doc))
    println(pretty.layout(src))
    // obcs.foreach { case (k,v) =>
    //   println(s"Node ${k.pprString}")
    //   println(pretty.layout(pretty.indent(v.ppr)))
    // }


  def printSchedules()(f: Node.Invocation => Node): Unit =
    given builder: Builder = new Builder(lack.meta.core.node.Builder.Node.top())
    builder.invoke(f)
    val subnodes = builder.nodeRef.allNodes

    subnodes.foreach { n =>
      val nn = n.freeze
      val graph = Schedule.Slurp(nn).graph()
      println(pretty.layout(nn.pprWithSubnodes(List())))
      println(s"Edges ${nn.name.pprString}:")
      graph.edges.entries.foreach { case (k,v) =>
        val pp = pretty.parens(k.ppr) <+> pretty.text(">") <+>
          pretty.tupleP(v.toList)
        println(pretty.layout(pretty.indent(pp)))
      }

      println(s"Schedule ${nn.name.pprString}:")
      Schedule.scheduleWithNode(nn, graph).entries.foreach { case k =>
        println(pretty.layout(pretty.indent(k.ppr)))
      }

    }

  def schedules(nodes: Iterable[core.node.Node]): names.immutable.RefMap[Schedule] =
    val scheds = nodes.map { n =>
      val graph = Schedule.Slurp(n).graph()
      val sched = Schedule.scheduleWithNode(n, graph)
      n.name -> sched
    }
    SortedMap.from(scheds)
