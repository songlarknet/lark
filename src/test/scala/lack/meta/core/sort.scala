package lack.meta.core

import lack.meta.base.names
import lack.meta.test.hedgehog._

package object sort:

  /** Generator for sorts. */
  object G:
    /** Primitive sorts */
    object logical:
      val numeric = Gen.elementIndexed_(Sort.Table.logical.numeric)
      val all = Gen.elementIndexed_(Sort.Table.logical.all)

    /** Sorts with a runtime representation */
    object runtime:
      val ints = Gen.elementIndexed_(Sort.Table.runtime.ints)

    val all = Gen.elementIndexed_(Sort.Table.all)

    def env(range: Range[Int], sorts: Gen[Sort]): Gen[term.Check.Env] =
      (for i <- component
          s <- sorts
      yield (names.Ref.fromComponent(i),s)).list(range).map(kvs => scala.collection.immutable.SortedMap.from(kvs))

    val componentSymbol: Gen[names.ComponentSymbol] =
      for b <- lack.meta.test.Corpus.birds
      yield names.ComponentSymbol.fromScalaSymbol(b)

    val component: Gen[names.Component] =
      for b <- componentSymbol
      yield names.Component(b)
