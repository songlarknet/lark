package lark.test.base.names

import lark.meta.base.names

import lark.test.hedgehog._
import lark.test.Corpus

/** Generator for names and things. */
object G:

  /** A fully-qualified name */
  def qualifiedRef: Gen[names.Ref] =
    for
      prefix <- component.list(Range.linear(0, 10))
      name <- component
    yield names.Ref(prefix, name)

  /** Generate a single component name, qualified by the prefix given */
  def ref(prefix: names.Prefix): Gen[names.Ref] =
    for c <- component
    yield prefix(c)

  /** Generate a single component name, unqualified */
  def ref1: Gen[names.Ref] =
    ref(names.Prefix(List()))

  def component: Gen[names.Component] =
    for b <- componentSymbol
        ix <-
         Gen.constant(None)
            .rarely(
             Gen.int(Range.linear(0, 100))
                .map(Some(_)))
    yield names.Component(b, ix)

  def componentSymbol: Gen[names.ComponentSymbol] =
    componentSymbolWord(Corpus.birds)
      .rarely(componentSymbolArbitrary)

  def componentSymbolWord(words: Gen[String]): Gen[names.ComponentSymbol] =
    for w <- words
    yield names.ComponentSymbol.fromScalaSymbol(w)

  def componentSymbolArbitrary: Gen[names.ComponentSymbol] =
    for
      c <- startChar
      cs <- Gen.string(midChar, Range.linear(0, 20))
    yield names.ComponentSymbol.fromStringUnsafe(c + cs)


  /** Valid start characters for a ComponentSymbol.
   *
   * ComponentSymbol defines a set of internal symbols that should never clash
   * with user symbols. These internal symbols all start with a caret. To avoid
   * any possible clash, don't generate any carets here, but do generate them
   * in midChar.
   */
  val startChar =
    Gen.choice1(
      Gen.alpha,
      Gen.elementIndexed("!#$%&*-_=+/<>".toIndexedSeq))

  /** Valid middle characters for a ComponentSymbol */
  val midChar =
    Gen.choice1(
      startChar,
      Gen.digit,
      Gen.constant('@'),
      Gen.constant('^'))
