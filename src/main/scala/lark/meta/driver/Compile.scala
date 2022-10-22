package lark.meta.driver

import lark.meta.base.names
import lark.meta.base.names.given
import lark.meta.base.pretty
import lark.meta.core
import lark.meta.core.node.Schedule
import lark.meta.target

import lark.meta.source.Compound.{given, _}
import lark.meta.source.Compound.implicits._
import lark.meta.source.Stream
import lark.meta.source.Stream.{SortRepr, Bool, UInt8}
import lark.meta.source.node.{Base, Invocation}

import scala.collection.immutable.SortedMap
import java.nio.file.{Path, Files, Paths}
import scala.reflect.ClassTag

/** Compile a program to executable code. */
object Compile:
  def compile[T <: Base: ClassTag]
    (basename: String = "lark", output: Option[Path] = None)
    (body: Invocation => T)
    (using location: lark.meta.macros.Location)
  : Unit =
    val subnodes = Invoke.allNodes(body)
    val frozen   = subnodes.map(_.freeze)
    val sliced   = core.node.Slice.program(frozen)
    val checked  = core.node.Check.program(sliced, core.node.Check.Options())
    val scheds   = schedules(sliced)
    val program  = core.obc.FromNode.program(sliced, scheds)

    // obcs.foreach { case (k,v) =>
    //   println(s"Node ${k.pprString}")
    //   println(pretty.layout(pretty.indent(v.ppr)))
    // }

    core.obc.Check.program(program, core.obc.Check.Options())

    val opts   = target.C.Options(basename = basename, program = program)
    val header = target.C.header(opts)
    val source = target.C.source(opts)

    output match
      case None =>
        println(pretty.layout(header))
        println(pretty.layout(source))
      case Some(p) =>
        val h = p.resolve(basename + ".h")
        val c = p.resolve(basename + ".c")
        Files.writeString(h, pretty.layout(header))
        Files.writeString(c, pretty.layout(source))


  def printSchedules[T <: Base: ClassTag]
    (body: Invocation => Base)
    (using location: lark.meta.macros.Location)
  : Unit =
    val subnodes = Invoke.allNodes(body)

    subnodes.foreach { n =>
      val nn = n.freeze
      println(s"Schedule ${nn.name.pprString}:")
      Schedule.schedule(nn).entries.foreach { case k =>
        println(pretty.layout(pretty.indent(k.ppr)))
      }

    }

  def schedules(nodes: Iterable[core.node.Node]): names.immutable.RefMap[Schedule] =
    val scheds = nodes.map { n =>
      n.name -> Schedule.schedule(n)
    }
    SortedMap.from(scheds)
