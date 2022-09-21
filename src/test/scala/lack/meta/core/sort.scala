package lack.meta.core

import lack.meta.test.hedgehog._

package object sort:

  /** Generator for sorts. */
  object G:
    val numeric: Gen[Sort] =
      Gen.elementIndexed(Sort.Table.numeric.toIndexedSeq)

    val any: Gen[Sort] =
      Gen.elementIndexed(Sort.Table.base.toIndexedSeq)
