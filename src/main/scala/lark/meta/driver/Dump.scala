package lark.meta.driver

import lark.meta.base.pretty
import lark.meta.base.debug.{Stage, Substage, File, Stdout, Quiet}

/** Tools for inspecting intermediate outputs.
 *
 * This package defines a sequence of stages that can be printed to stdout
 * or file. Stages can be specified by listing them explicitly, along with
 * an output mode. If an output mode is specified with no stages, then all
 * stages are dumped. Files are dumped to project/dump inside the sbt build
 * directory, unless a path is specified.
 *
 * To dump all stages to project/dump:
 * > Compile.compile(Compile.Options().dump(Dump.file()))
 *
 * To dump just the simplified program to stdout:
 * > Compile.compile(Compile.Options().dump(Dump.stdout(Dump.Prepare.Simp)))
 */
object Dump:
  object Prepare extends Stage("00-prep", "Common preparation", ".lark"):
    object Input extends Substage(Prepare, "00-input", "Input")
    object Slice extends Substage(Prepare, "10-slice", "Sliced outputs")
    object Simp extends Substage(Prepare, "20-simp", "Simplified")
    object Typecheck extends Substage(Prepare, "30-tcheck", "Typecheck")

  object Check extends Stage("10-check", "Model checking", ".smt", "; "):
    object System extends Substage(Check, "00-system", "Labelled transition system", Some(".lts"), Some("// "))
    object Bmc extends Substage(Check, "1x-bmc", "Bounded model checking (SMT)")
    object Kind extends Substage(Check, "1x-kind", "K-inductive checking (SMT)")
    object Feas extends Substage(Check, "1x-feas", "Feasibility checking (SMT)")

  object Compile extends Stage("10-compile", "Compile", ""):
    object Schedule extends Substage(Compile, "00-sched", "Schedule", Some(".log"))
    object Obc extends Substage(Compile, "10-obc", "Generated Object-C", Some(".obc"))
    object C extends Substage(Compile, "20-c", "Generated C code", Some(".c"))

  object Grind extends Stage("20-grind", "Grind", ".log"):
    object Trace extends Substage(Grind, "00-trace", "Trace")
    object Eval extends Substage(Grind, "10-c", "Grinding evaluator")
    object C extends Substage(Grind, "20-c", "Grinding C code", Some(".c"))

  /** Print intermediate stages to standard output. */
  def stdout(stages: Stage*): Dump =
    lark.meta.base.debug.Options(Set(stages*), Stdout)

  /** Write intermediate stages to file. */
  def file(stages: Stage*): Dump =
    path("project/dump", stages*)

  /** Write intermediate stages to file with given path. */
  def path(path: java.nio.file.Path, stages: Stage*): Dump =
    lark.meta.base.debug.Options(Set(stages*), File(path))

  /** Write intermediate stages to file with given path. */
  def path(pathString: String, stages: Stage*): Dump =
    path(java.nio.file.Paths.get(pathString), stages*)

  /** Do not dump anything. This is the default mode. */
  def quiet =
    lark.meta.base.debug.Options(Set.empty, Quiet)

type Dump = lark.meta.base.debug.Options