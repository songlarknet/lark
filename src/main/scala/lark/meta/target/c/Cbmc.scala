package lark.meta.target.c

import lark.meta.base.pretty

import java.nio.file.{Files, Path, Paths}
import java.lang.ProcessBuilder
import java.lang.Process

/** Helper for checking code with CBMC.
 *
 * This is used for testing.
 */
object Cbmc:
  /** Check the given C source. Code should be a complete C file. */
  def check(code: pretty.Doc, options: List[String] = defaults) =
    import java.nio.file.{Files, Paths}
    val tmp = Files.createTempDirectory("lark-cbmc")
    val src = tmp.resolve("input.c")
    val out = tmp.resolve("output.log")
    Files.writeString(src, pretty.layout(code))

    val pb = cbmc(src, options)
    pb.redirectErrorStream(true)
    pb.redirectOutput(ProcessBuilder.Redirect.appendTo(out.toFile()))
    val proc = pb.start()
    proc.waitFor()
    val exitCode = proc.exitValue()
    if (exitCode != 0)
      val log = Files.readString(out)
      throw new Exception("CBMC failed. Log:" + "\n" + log + "CBMC failed. Log above.")

    // Might be OK to keep them around if it fails
    Files.delete(src)
    Files.delete(out)
    Files.delete(tmp)

  def cbmc(path: Path, options: List[String]): ProcessBuilder =
    val bin = sys.env
      .get("LARK_CBMC_BIN")
      .getOrElse("cbmc")

    val args = List(
      bin,
      path.toString) ++
      options

    val pb = ProcessBuilder(args : _*)
    pb

  val arith_checks =
    // Disable unsigned-overflow-check as "-0u" triggers it, but since the value is OK it doesn't trigger the evaluator.
    List("--div-by-zero-check", "--signed-overflow-check", "--conversion-check")
    // List("--div-by-zero-check", "--signed-overflow-check", "--unsigned-overflow-check", "--conversion-check")
  val trace =
    List("--compact-trace")
  val dCBMC =
    List("-DCBMC=1")

  val rts = sys.env
    .get("LARK_RTS_C")
    .getOrElse("src/rts/c")

  val defaults = arith_checks ++ trace ++ dCBMC ++ List("-I", rts)
