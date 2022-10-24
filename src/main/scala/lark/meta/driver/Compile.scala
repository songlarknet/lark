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
    (options: Options = Options())
    (body: Invocation => T)
    (using location: lark.meta.macros.Location)
  : Unit =
    val compiled = getCompiled(options, body)
    // Put in the sbt build directory if no output path specified
    val path = options.output.getOrElse(Paths.get("project/lark"))
    Files.createDirectories(path)

    val h = path.resolve(options.basename + ".h")
    val c = path.resolve(options.basename + ".c")
    Files.writeString(h, pretty.layout(compiled.headerC))
    Files.writeString(c, pretty.layout(compiled.sourceC))

  def getCompiled[T <: Base: ClassTag]
    (options: Options, body: Invocation => T)
    (using location: lark.meta.macros.Location)
  : Compiled =
    val prepared = Prepare.prepareCompile(options.dump, body)
    val scheds   = schedules(prepared.simped, options.dump)
    val program  = core.obc.FromNode.program(prepared.simped, scheds)

    options.dump.traceP(program, Dump.Compile.Obc)
    core.obc.Check.program(program, core.obc.Check.Options())

    val opts   = options.withCOptions(target.C.Options(basename = options.basename, program = program))
    val header = target.C.header(opts)
    val source = target.C.source(opts)

    val compiledP =
      header <@>
      source

    options.dump.trace(compiledP, Dump.Compile.C)

    Compiled(prepared, scheds, program, opts, header, source)

  def schedules(nodes: Iterable[core.node.Node], dump: Dump): names.immutable.RefMap[Schedule] =
    val scheds = nodes.map { n =>
      n.klass -> Schedule.schedule(n)
    }

    val schedsP =
      for (n,s) <- scheds
      yield new pretty.Pretty:
        def ppr = pretty.text("Schedule") <+> pretty.nest(n.ppr <> pretty.colon <@>
          pretty.vsep(s.entries.map(_.ppr)))
    dump.traces(schedsP, Dump.Compile.Schedule)

    SortedMap.from(scheds)

  case class Compiled(
    prepared:  Prepare.Prepared,
    schedules: names.immutable.RefMap[Schedule],
    obcs:      core.obc.Obc.Program,
    optsC:     target.C.Options,
    headerC:   pretty.Doc,
    sourceC:   pretty.Doc)

  case class Options(
    basename: String         = "lark",
    output: Option[Path]     = None,
    dump:  Dump              = Dump.quiet,
    withCOptions: target.C.Options => target.C.Options
                             = identity
  ):
    def dump(dump: Dump): Options =
      this.copy(dump = dump)