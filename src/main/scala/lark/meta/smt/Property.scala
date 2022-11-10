package lark.meta.smt

import lark.meta.base.{debug, names, pretty}
import lark.meta.core.Prop

sealed case class Property(
  judgment: system.SystemJudgment,
  bmc:  Property.Disprove = Property.Disprove(Property.Unknown, 0),
  kind: Property.Prove    = Property.Prove(Property.Unknown, 0),
  feas: Property.Disprove = Property.Disprove(Property.Unknown, 0),
) extends pretty.Pretty:
  val (status, pprDoc) =
    (bmc.status, kind.status, feas.status) match
      case (Property.Safe, Property.Safe, Property.Safe) =>
        if bmc.steps >= kind.steps
        then (Property.Safe, pretty.text("OK"))
        else (Property.Unknown, pretty.text(s"unknown: induction needs ${kind.steps} steps"))
      case (Property.Unsafe, _, _) =>
        (Property.Unsafe, pretty.text(s"counterexample"))
      case (_, _, Property.Unsafe) =>
        (Property.Unsafe, pretty.text(s"infeasible"))
      case (_, Property.Unsafe, _) =>
        (Property.Unknown, pretty.text(s"unknown: induction failed (true for ${bmc.steps} steps)"))
      case (_, _, _) =>
        (Property.Unknown, pretty.text(s"unknown"))

  def ppr = pprDoc

  val ok = status == Property.Safe

  def join(that: Property): Property =
    Property(judgment, this.bmc.join(that.bmc), this.kind.join(that.kind), this.feas.join(that.feas))

  def withBmc(bmc: Property.Disprove): Property =
    Property(judgment, this.bmc.join(bmc), this.kind, this.feas)

  def withKind(kind: Property.Prove): Property =
    Property(judgment, this.bmc, this.kind.join(kind), this.feas)

  def withFeas(feas: Property.Disprove): Property =
    Property(judgment, this.bmc, this.kind, this.feas.join(feas))

object Property:

  type Map = scala.collection.immutable.Map[Prop.Judgment, Property]
  object Map:
    export scala.collection.immutable.Map._

    def join(map1: Map, map2: Map): Map =
      map2.foldLeft(map1) { case (acc, (ref, prop)) =>
        val propX = acc.get(ref).fold(prop)(_.join(prop))
        acc + (ref -> propX)
      }


  sealed trait Status extends pretty.Pretty

  // TODO distinguish between an "explicit" unknown SMT result and a "haven't asked the right question yet" unknown
  case object Safe extends Status:
    def ppr = pretty.text("Safe")
  case object Unsafe extends Status:
    def ppr = pretty.text(s"Unsafe")
  case object Unknown extends Status:
    def ppr = pretty.text(s"Unknown")

  /**
   * Interpreting statuses as trying to disprove a property.
   * "Safe" is interpreted as being unable to prove or disprove the property
   * at that step, while "Unsafe" is interpreted as definitive evidence that
   * the property is false at that step (eg a counterexample).
  */
  sealed case class Disprove(status: Status, steps: Int) extends pretty.Pretty:
    def ppr = status match
      case Safe =>
        pretty.text(s"Safe for at least ${steps} steps")
      case Unsafe =>
        pretty.text(s"Unsafe at ${steps} steps")
      case Unknown =>
        pretty.text(s"Unknown at ${steps} steps")

    def at(i: Int): Status =
      status match
        case Safe =>
          if i <= steps then Safe else Unknown
        case Unsafe =>
          // if i < steps then Safe else Unsafe ?
          Unsafe
        case Unknown =>
          Unknown

    /**
     * Join two statuses together. Should be commutative and associative.
     *
     * If it's bad at step n, then it's bad at any step afterwards:
     * > d.at(i) == Unsafe ==> d.at(i + n) == Unsafe   for n >= 0
     *
     * If it's bad at step n, then any join is also bad at step n:
     * > d.at(i) == Unsafe ==> join(d, d').at(i) == Unsafe
     *
     * Similar properties should hold for unknown statuses. If it's unknown at
     * step n, then it's unknown at any step afterwards:
     * > d.at(i) == Unknown ==> d.at(i + n) == Unknown   for n >= 0
     *
     * Join doesn't remove knowledge - if it's not-unknown at step n, then any
     * join is also not-unknown at step n:
     * > d.at(i) != Unknown ==> join(d, d').at(i) != Unknown
    */
    def join(that: Disprove): Disprove =
      (this.status, that.status) match
        case (Unsafe, Unsafe) =>
          Disprove(Unsafe, this.steps.min(that.steps))
        case (Unsafe, _) =>
          this
        case (_, Unsafe) =>
          that
        case (Safe, Safe) =>
          Disprove(Safe, this.steps.max(that.steps))
        case (Safe, _) =>
          this
        case (_, Safe) =>
          that
        case (Unknown, Unknown) =>
          Disprove(Unknown, this.steps.min(that.steps))

  /**
   * Interpreting statuses as trying to prove a property.
   * "Safe" is interpreted as proof that the property holds at that step
   * and all successive steps, while "Unsafe" is interpreted as being unable
   * to prove or disprove the property at that step.
   */
  sealed case class Prove(status: Status, steps: Int) extends pretty.Pretty:
    def ppr = status match
      case Safe =>
        pretty.text(s"Safe from ${steps} steps")
      case Unsafe =>
        pretty.text(s"Unsafe up to ${steps} steps")
      case Unknown =>
        pretty.text(s"Unknown at ${steps} steps")

    def at(i: Int): Status =
      status match
        case Safe =>
          Safe
        case Unsafe =>
          if i <= steps then Unsafe else Unknown
        case Unknown =>
          Unknown

    /**
     * Join two statuses together. Should be commutative and associative.
     *
     * If it's good at step n, then it's good at any step afterwards:
     * > d.at(i) == Safe ==> d.at(i + n) == Safe   for n >= 0
     *
     * If it's good at step n, then any join is also good at step n:
     * > d.at(i) == Safe ==> join(d, d').at(i) == Safe
     */
    def join(that: Prove): Prove =
      (this.status, that.status) match
        case (Safe, Safe) =>
          Prove(Safe, this.steps.min(that.steps))
        case (Safe, _) =>
          this
        case (_, Safe) =>
          that
        case (Unsafe, Unsafe) =>
          Prove(Unsafe, this.steps.max(that.steps))
        case (Unsafe, _) =>
          this
        case (_, Unsafe) =>
          that
        case (Unknown, Unknown) =>
          Prove(Unknown, this.steps.max(that.steps))

