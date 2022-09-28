package lack.test

import _root_.{munit => m}
import _root_.{hedgehog => h}
import h.core.PropertyConfig
import h.{runner => hr}

object suite:

  /** Cast from return of assert (unit) to a result. */
  implicit def badbadbadbadbad(u: Unit): h.core.Result =
    h.Result.Success

  /** Set the GRIND MULTIPLIER to >1 to increase the number of tests. */
  val HEDGEHOG_GRIND =
    sys.env
      .get("HEDGEHOG_GRIND")
      .flatMap(_.toIntOption)
      .getOrElse(1)

  /** Property test suite.
   *
   * hedgehog.munit.HedgehogSuite has a "HedgehogAssertions" which hides the
   * assertion functions assert, assertEquals etc, by shadowing them with ones
   * that return a hedgehog.Result. But if you accidentally use these in a
   * unit test, your failures will be silently discarded.
   * I'd rather just use exception-style assertions everywhere, even in
   * property tests.
   */
  abstract class HedgehogSuite extends m.FunSuite with m.Assertions:
    val sub = new h.munit.HedgehogSuite() { }

    def property(
        name: String,
        withConfig: PropertyConfig => PropertyConfig = identity
    )(
        prop: => h.Property
    )(implicit loc: m.Location): Unit =
      val old = sub.munitTestsBuffer.length

      def withConfigX(c: PropertyConfig) =
        val cX = withConfig(c)
        cX.copy(
          testLimit    = cX.testLimit.value * HEDGEHOG_GRIND,
          discardLimit = h.core.DiscardCount(cX.discardLimit.value * HEDGEHOG_GRIND))

      sub.property(name, withConfigX)(prop)
      munitTestsBuffer ++= sub.munitTestsBuffer.drop(old)

  // /** These tests both succeed with munit.HedgehogSuite */
  // class PX extends suite.HedgehogSuite:
  //   property("multiple assertions") {
  //     for
  //       i <- h.Gen.int(h.Range.linear(0, 10)).log("i")
  //     yield
  //       assert(i > 100)
  //       assert(true)
  //   }

  //   test("wrong assertion type") {
  //     val i = 10
  //     assert(i > 100)
  //   }
