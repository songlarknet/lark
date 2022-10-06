package lack.test.core

import lack.meta.base
import lack.meta.base.names.Ordering_Ref
import lack.meta.core.term
import lack.meta.core.Sort

import lack.test.hedgehog._
import lack.test.Corpus

package object sort:

  /** Generator for sorts. */
  object G:
    val names = lack.test.base.names.G

    /** Primitive sorts */
    object logical:
      val numeric = Gen.elementIndexed_(Sort.Table.logical.numeric)
      val all = Gen.elementIndexed_(Sort.Table.logical.all)

    /** Sorts with a runtime representation */
    object runtime:
      val ints = Gen.elementIndexed_(Sort.Table.runtime.ints)
      val all = Gen.elementIndexed_(Sort.Table.runtime.all)

    val all = Gen.elementIndexed_(Sort.Table.all)

    def env(range: Range[Int], sorts: Gen[Sort]): Gen[term.Check.Env] =
      (for i <- names.component
          s <- sorts
      yield (base.names.Ref.fromComponent(i),s)).list(range).map(kvs => scala.collection.immutable.SortedMap.from(kvs))

    def subenv(env: term.Check.Env): Gen[term.Check.Env] =
      Gen.sublist(env.toList)
        .map(scala.collection.immutable.SortedMap.from(_))
