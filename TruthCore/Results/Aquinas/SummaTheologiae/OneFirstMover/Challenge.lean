import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question11.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Case.Catholicism.StageOneBridges
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  FirstUnmovedMoverHasEveryPerfection FirstUnmovedMoversIdenticalOrDistinct
  FirstUnmovedMoverIsFirstBeing)
/-- ST I q.11 a.3 co., second proof, for the *prima via*'s mover. If there were
two first movers moved by none, they would differ in some act: one in act in a
respect in which the other is not. Then the other would lack a perfection, but
each has every perfection (open bridge). So two first movers are not distinct,
and, given that they are either the same or distinct, they are the same.
Discharges the #159 gap statement `AtMostOneFirstUnmovedMover`. -/
theorem oneFirstMover {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (hPerfect : FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct)
    (hDiffer : PluralFirstMoversWouldDifferInActReading MovedIn MovesIn InAct)
    (hEither : FirstUnmovedMoversIdenticalOrDistinct MovedIn MovesIn) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  sorry

/-- The *prima via*'s premises (#151) and every premise of the #165 results hold
together in one finite model, so none of the results follows from inconsistent
premises. The model also witnesses a per se link, a moving body, a composite with
a component, matter-form composition and an esse other than an essence, so those
premises are not satisfied only through false antecedents.

`PluralFirstMoversWouldDifferInActReading` holds only vacuously here, as it must
in any model of all the premises: with every perfection it rules out two first
movers. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Principle : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply ComponentOf : Being → Being → Prop)
      (Body ComposedOfMatterAndForm Composite : Being → Prop)
      (essenceOf esseOf : Being → Principle),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply ∧
      NoBodyMovesUnlessMovedReading MovedIn MovesIn Body ∧
      CompositePosteriorToComponentsReading ComponentOf PriorSimply ∧
      CompositeHasComponentOtherThanItselfReading Composite ComponentOf ∧
      MatterFormAndEsseEssenceAreCompositionsReading
        ComposedOfMatterAndForm Composite essenceOf esseOf ∧
      FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct ∧
      PluralFirstMoversWouldDifferInActReading MovedIn MovesIn InAct ∧
      FirstUnmovedMoversIdenticalOrDistinct MovedIn MovesIn ∧
      (∃ y x, MovesAsMoved y x) ∧
      (∃ b x r, Body b ∧ MovesIn b x r) ∧
      (∃ b p, ComposedOfMatterAndForm b ∧ ComponentOf p b ∧ esseOf b ≠ essenceOf b) := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
