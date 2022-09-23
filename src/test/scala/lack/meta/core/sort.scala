package lack.meta.core

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