package lack.test.base.names

import lack.meta.base.names

import lack.test.hedgehog._
import lack.test.suite._

class P extends HedgehogSuite:
  property("names.Ref roundtrip Ref=>String=>Ref") {
    for
      ref    <- G.qualifiedRef.ppr("ref")
      str    <- Property.ppr(ref.pprString, "str")
      parsed <- Property.ppr(names.Ref.parseFromString(str), "parsed")
    yield
      assertEquals(parsed, Some(ref))
  }

  property("names.Ref roundtrip String=>Ref=>String (allowed chars)",
    withConfig = _.copy(discardLimit = hedgehog.core.DiscardCount(100000))
  ) {
    val chars = Gen.choice1(
      G.startChar,
      G.midChar,
      Gen.constant('?'),
      Gen.constant('.'))
    propStringRefString(Gen.string(chars, Range.linear(0, 10)))
  }

  property("names.Ref roundtrip String=>Ref=>String (full ascii)",
    withConfig = _.copy(discardLimit = hedgehog.core.DiscardCount(100000))
  ) {
    propStringRefString(Gen.string(Gen.ascii, Range.linear(0, 10)))
  }

  def propStringRefString(strG: Gen[String]) =
    for
      str    <- strG.forAll
      parsed  = names.Ref.parseFromString(str)
      _      <-
        if parsed.isDefined
        then Property.point(())
        else Property.discard
      // Display the characters as integers, bad chars can mess up the test display
      _ <- Property.ppr(str.toList.map(_.toInt), "str.chars")
      _ <- Property.ppr(parsed.get.pprString.toList.map(_.toInt), "parsed.chars")
    yield
      Result.diff(parsed.get.pprString, str)(_ == _)
