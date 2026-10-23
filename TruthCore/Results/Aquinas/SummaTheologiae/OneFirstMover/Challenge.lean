import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question11.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Case.Catholicism.StageOne
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  FirstUnmovedMoverIsPureAct)
/-- ST I q.11 a.3 co., second proof, for the *prima via*'s mover: two first
movers moved by none would each have every perfection, so they would agree in
every act, and beings that agree in every act are one. Discharges the #159 gap
statement `AtMostOneFirstUnmovedMover`. -/
theorem oneFirstMover {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (hPerfect : FirstUnmovedMoverHasEveryPerfectionReading MovedIn MovesIn InAct)
    (hDiffer : ManyMustDifferReading InAct) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  sorry

/-- The premises of the #165 results are jointly satisfiable with the *prima
via*'s premises (#151), in a model where they are not all vacuous: `f` moves
`x`; `x` is moved, in potency, a body, composite, composed of matter and form,
simply posterior to `f`, and has an esse other than its essence. So none of the
results follows from inconsistent premises. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Principle : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (Body ComposedOfMatterAndForm Composite : Being → Prop)
      (essenceOf esseOf : Being → Principle),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      NoBodyMovesUnlessMovedReading MovedIn MovesIn Body ∧
      FirstUnmovedMoverIsFirstBeingReading MovedIn MovesIn PriorSimply ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      MatterIsInPotencyReading InPotency ComposedOfMatterAndForm ∧
      EsseOtherThanEssenceIsPotencyReading InPotency essenceOf esseOf ∧
      CompositeIsInPotencyReading InPotency Composite ∧
      FirstUnmovedMoverHasEveryPerfectionReading MovedIn MovesIn InAct ∧
      ManyMustDifferReading InAct ∧
      (∃ b, Body b ∧ ComposedOfMatterAndForm b ∧ Composite b ∧ esseOf b ≠ essenceOf b) := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
