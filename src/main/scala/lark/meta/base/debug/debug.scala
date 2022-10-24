package lark.meta.base

package object debug:
  class Stage(
    val id:            String,
    val name:          String,
    val extension:     String,
    val headerComment: String = "// ",
  ):
    def ids     = lineage.map(_.id)
    def lineage = List(this)

  class Substage(
    val parent:    Stage,
    id:            String,
    name:          String,
    extension:     Option[String] = None,
    headerComment: Option[String] = None)
  extends Stage(id, name, extension.getOrElse(parent.extension), headerComment.getOrElse(parent.headerComment)):
    override def ids = parent.ids :+ id
    override def lineage = parent.lineage :+ this

  case class Options(
    stages: Set[Stage],
    dump: Dump
  ):
    def withTrace[U](stage: Stage, key: Option[String] = None)(body: Sink => U): U =
      val config = Dump.Config(stage, key)
      if stages.isEmpty || stage.lineage.exists(stages.contains(_))
      then
        val sink = dump.sink(Dump.Config(stage, key))
        try
          body(sink)
        finally
          sink.close()
      else
        body(Quiet.sink(config))

    def trace(value: => pretty.Doc, stage: Stage, key: Option[String] = None): Unit =
      val ppr = new pretty.Pretty:
        def ppr = value
      traces(List(ppr), stage, key)

    def traceP(value: pretty.Pretty, stage: Stage, key: Option[String] = None): Unit =
      traces(List(value), stage, key)

    def traces[T <: pretty.Pretty](values: Iterable[T], stage: Stage, key: Option[String] = None): Unit =
      withTrace(stage, key) { sink =>
        values.foreach(sink.write(_))
      }

  trait Dump:
    def sink(config: Dump.Config): Sink

  object Dump:
    case class Config(
      stage: Stage,
      key:   Option[String],
    ):
      val ids      = stage.ids
      val filename = ids.mkString(".") + key.fold("")("_" + _) + stage.extension

      def header =
        stage.headerComment + " Lark debug: dump for stage " + filename + ": " + stage.name + " " + java.time.LocalDateTime.now + "\n"

  trait Sink:
    def write(value: pretty.Pretty): Unit
    def write(value: => pretty.Doc): Unit =
      write(new pretty.Pretty:
        def ppr = value)
    def close(): Unit

  case object Quiet extends Dump:
    def sink(config: Dump.Config): Sink = sink
    val sink = new Sink:
      def write(value: pretty.Pretty): Unit = ()
      def close(): Unit = ()

  case object Stdout extends Dump:
    def sink(config: Dump.Config): Sink = new Sink:
      def write(value: pretty.Pretty): Unit =
        Stdout.write(config, value)
      def close(): Unit = ()

    private var lastConfig: Option[Dump.Config] = None
    private def write(config: Dump.Config, value: pretty.Pretty) =
      if lastConfig != Some(config)
      then
        println("")
        println(pretty.layout(pretty.Colour.Grey.of(config.header)))
      lastConfig = Some(config)
      println(value.pprString)

  case class File(path: java.nio.file.Path = java.nio.file.Paths.get("")) extends Dump:
    def sink(config: Dump.Config): Sink =
      java.nio.file.Files.createDirectories(path)
      val fname  = path.resolve(config.filename)
      val writer = java.nio.file.Files.newBufferedWriter(fname)
      writer.write(config.header)
      writer.write("\n")

      new Sink:
        def write(value: pretty.Pretty): Unit =
          writer.write(value.pprString)
          writer.write("\n")
        def close(): Unit =
          writer.close()

