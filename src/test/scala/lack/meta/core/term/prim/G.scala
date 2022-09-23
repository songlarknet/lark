package lack.meta.core.term.prim

import lack.meta.base.pretty
import lack.meta.core
import lack.meta.core.term.Prim
import lack.meta.core.sort.Sort

import lack.meta.test.hedgehog._

/** Generator for primitives */
case class G(table: IndexedSeq[G.PrimEntry] = G.table.toIndexedSeq):

  val lookup = table.map(pe => (pe.prim, pe)).toMap

  /** Generate any primitive, returning the argument and result sorts. */
  def prim(): Gen[(Prim, List[Sort], Sort)] =
    for
      pe <- Gen.elementIndexed(table)
      as <- pe.args()
      p   = pe.prim
      r   = p.sort(as)
    yield (p, as, r)

  /** Generate a primitive with result sort 'res', returning the primitive
    * and argument sorts.
    * Throws an exception if no primitive matches - this probably means the
    * primitive table is incomplete.
    */
  def result(res: Sort): Gen[(Prim, List[Sort])] =
    for
      pes <- cut
      poss = pes.flatMap(pe => pe.args(res).map((pe.prim, _)))
      pas  = poss.headOption.getOrElse {
        throw new Exception(
          s"""can't generate primitive returning sort ${res.pprString}.
             |This probably means the table is incomplete.
             |Table: ${pretty.layout(pretty.tupleP(table.map(_.prim)))}""".stripMargin)
      }
      p    = pas._1
      as  <- pas._2
    yield (p, as)

  /** Generate a primitive that can be partially applied with argument sorts
    * 'prefix', returning the primitive and remaining argument sorts.
    * Throws an exception if no primitive matches - this probably means the
    * primitive table is incomplete or the generation code is whacked out.
    */
  def partial(prefix: List[Sort]): Gen[(Prim, List[Sort], Sort)] =
    for
      pes <- cut
      poss = pes.flatMap(pe => pe.partial(prefix).map((pe.prim, _)))
      pas  = poss.headOption.getOrElse {
        throw new Exception(
          s"""can't generate primitive partially applied to ${pretty.layout(pretty.tupleP(prefix))}.
             |This might mean the table is incomplete, or generation is broken.
             |Table: ${pretty.layout(pretty.tupleP(table.map(_.prim)))}""".stripMargin)
      }
      p    = pas._1
      as  <- pas._2
      r    = p.sort(prefix ++ as)
    yield (p, as, r)

  /** Cut the deck of tables so it starts at a random point */
  private def cut: Gen[Iterable[G.PrimEntry]] =
    for
      i <- Gen.int(Range.constant(0, table.length))
    yield table.drop(i) ++ table.take(i)


/** Generator for primitives */
object G:

  /** How to generate argument types for a given primitive */
  trait PrimEntry:
    def prim: Prim

    /** Generate a list of argument sorts for this primitive.
     * > for as <- args().forall
     * > assertNoThrow(prim.check(as))
     */
    def args(): Gen[List[Sort]]

    /** Generate a list of argument sorts for given result.
     * Returns None if primitive cannot return given type.
     *
     * > for as  <- args(r)
     * >     as_ <- as.forall
     * > yield (prim.check(as_) == r)
     */
    def args(result: Sort): Option[Gen[List[Sort]]]

    /** Generate the remaining argument sorts for a partial application.
     * Returns None if arguments don't make sense for primitive.
     *
     * > for rest  <- partial(prefix)
     * >     rest_ <- rest.forall
     * > assertNoThrow(prim.check(prefix ++ rest_))
     */
    def partial(prefix: List[Sort]): Option[Gen[List[Sort]]]

  object PrimEntry:
    case class Simple(prim: Prim.Simple) extends PrimEntry:
      def args() = Gen.constant(prim.expect)

      def args(result: Sort) =
        if result == prim.ret
        then Some(Gen.constant(prim.expect))
        else None

      def partial(prefix: List[Sort]) =
        if prim.expect.startsWith(prefix)
        then Some(Gen.constant(prim.expect.drop(prefix.length)))
        else None

    case class Prim_nn_b(prim: Prim.Prim_nn_b) extends PrimEntry:
      def args() =
        for
          i <- core.sort.G.logical.numeric
        yield (List(i, i))

      def args(result: Sort) =
        if result == Sort.Bool
        then Some(args())
        else None

      def partial(prefix: List[Sort]) = prefix match
        case List() =>
          Some(args())
        case List(i) =>
          if i.isInstanceOf[Sort.Numeric]
          then Some(Gen.constant(List(i)))
          else None
        case List(i,j) =>
          if i.isInstanceOf[Sort.Numeric] && i == j
          then Some(Gen.constant(List()))
          else None
        case _ =>
          None

    case class Prim_nn_n(prim: Prim.Prim_nn_n) extends PrimEntry:
      def args() =
        for
          i <- core.sort.G.logical.numeric
        yield (List(i, i))

      def args(result: Sort) =
        if result.isInstanceOf[Sort.Numeric] && Sort.logical(result) == result
        then Some(Gen.constant(List(result, result)))
        else None

      def partial(prefix: List[Sort]) = prefix match
        case List() =>
          Some(args())
        case List(i) =>
          if i.isInstanceOf[Sort.Numeric]
          then Some(Gen.constant(List(i)))
          else None
        case List(i,j) =>
          if i.isInstanceOf[Sort.Numeric] && i == j
          then Some(Gen.constant(List()))
          else None
        case _ =>
          None

    case class Prim_n_n(prim: Prim) extends PrimEntry:
      def args() =
        for
          i <- core.sort.G.logical.numeric
        yield (List(i))

      def args(result: Sort) =
        if result.isInstanceOf[Sort.Numeric] && Sort.logical(result) == result
        then Some(Gen.constant(List(result)))
        else None

      def partial(prefix: List[Sort]) = prefix match
        case List() =>
          Some(args())
        case List(i) =>
          if i.isInstanceOf[Sort.Numeric]
          then Some(Gen.constant(List()))
          else None
        case _ =>
          None
    case class Prim_aa_b(prim: Prim) extends PrimEntry:
      def args() =
        for
          i <- core.sort.G.all
        yield (List(i, i))

      def args(result: Sort) =
        if result == Sort.Bool
        then Some(args())
        else None

      def partial(prefix: List[Sort]) = prefix match
        case List() =>
          Some(args())
        case List(i) =>
          Some(Gen.constant(List(i)))
        case List(i,j) =>
          if i == j
          then Some(Gen.constant(List()))
          else None
        case _ =>
          None
    case class Prim_baa_a(prim: Prim) extends PrimEntry:
      def args() =
        for
          i <- core.sort.G.all
        yield (List(Sort.Bool, i, i))

      def args(result: Sort) =
        Some(Gen.constant(List(Sort.Bool, result, result)))

      def partial(prefix: List[Sort]) = prefix match
        case List() =>
          Some(args())
        case List(i) =>
          if i == Sort.Bool
          then Some(args().map(_.drop(1)))
          else None
        case List(i,j) =>
          if i == Sort.Bool
          then Some(Gen.constant(List(j)))
          else None
        case List(i,j,k) =>
          if j == k
          then Some(Gen.constant(List()))
          else None
        case _ =>
          None

  val table = {
    import Table._
    List(
      PrimEntry.Simple(And),
      PrimEntry.Simple(Or),
      PrimEntry.Simple(Not),
      PrimEntry.Simple(Implies),
      PrimEntry.Prim_baa_a(Ite),
      PrimEntry.Prim_n_n(Negate),
      PrimEntry.Prim_nn_n(Add),
      PrimEntry.Prim_nn_n(Sub),
      PrimEntry.Prim_nn_n(Mul),
      PrimEntry.Prim_nn_n(Div),
      PrimEntry.Prim_nn_b(Le),
      PrimEntry.Prim_nn_b(Lt),
      PrimEntry.Prim_nn_b(Ge),
      PrimEntry.Prim_nn_b(Gt),
      PrimEntry.Prim_aa_b(Eq),
      )
  }
