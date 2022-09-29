package lack.meta.driver

import lack.meta.base.names
import lack.meta.base.pretty
import lack.meta.core.node.Schedule

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8}
import lack.meta.source.Node
import lack.meta.source.Node.{Builder}

object Compile:
  def compile(options: Options = Options())(f: Node.Invocation => Node): Unit =
    given builder: Builder = new Builder(lack.meta.core.node.Builder.Node.top())
    builder.invoke(f)
    val subnodes = builder.nodeRef.allNodes
    subnodes.foreach { n =>
      val nn = n.freeze
      val graph = Schedule.Slurp(nn).graph()
      println(pretty.layout(nn.pprWithSubnodes(List())))
      println(s"Edges ${names.Prefix(nn.path).pprString}:")
      graph.edges.entries.foreach { case (k,v) =>
        val pp = pretty.parens(k.ppr) <+> pretty.text(">") <+>
          pretty.tupleP(v.toList)
        println(pretty.layout(pretty.indent(pp)))
      }

      println(s"Schedule ${names.Prefix(nn.path).pprString}:")
      graph.scheduleWithNode(nn).foreach { case k =>
        println(pretty.layout(pretty.indent(k.ppr)))
      }

    }

  case class Options(
    verbose: Boolean = false,
  )
