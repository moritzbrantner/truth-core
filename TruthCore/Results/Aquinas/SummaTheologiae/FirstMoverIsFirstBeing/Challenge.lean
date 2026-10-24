import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
import TruthCore.Greek.Aristotle.Metaphysics
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsFirstBeing IsFirstUnmovedMover
  MaximeEnsIsGod SimplyPriorIsCauseOfBeing)

/-- The first-being bridge of #166, derived through the *quarta via*. Something
`m` is maximal in being (`quartaVia`). Nothing other than `m` is simply prior to
it: what is simply prior to `m` causes its being (open premise
`SimplyPriorIsCauseOfBeing`), a cause of another's being is more a being than it
(*Metaphysics* II.1), and nothing is more in being than `m`. Every first mover
moved by none is `m` (`firstMoverIsMaximeEns`), so it is the first being. -/
theorem firstMoverIsFirstBeing {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect) (God : Being → Prop)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGod : MaximeEnsIsGod InAct MoreIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hPriorCause : SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The q.105 a.5 premise is needed. In `Intelligence`, with `m` as God, every other
premise of `firstMoverIsFirstBeing` holds (excluded middle as decidable identity),
and so do the seven *prima via* premises and act's simple priority; but the first
mover moved by none `f` is caused by `m`, which is simply prior to it. An unmoved
mover caused in its being is possible unless caused agents are moved to act. -/
theorem withoutAppliedAgentNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect) (God : Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      MaximeEnsIsGod InAct MoreIn esse God →
      SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse →
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The open premise `MaximeEnsIsGod` is needed. In `Intelligence` with no being as
God, every other premise of `firstMoverIsFirstBeing` holds (the q.105 a.5 premise
vacuously), and so do the *prima via* premises and act's simple priority, but the
bridge fails as before. q.105 a.5 bears on the *quarta via*'s maximal being only
if that being is the God of which q.105 a.5 speaks. -/
theorem withoutMaximeEnsIsGodNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect) (God : Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God →
      SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse →
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The open premise `SimplyPriorIsCauseOfBeing` is needed. In `MutualPriority`, with
`m` as God, every other premise of `firstMoverIsFirstBeing` holds (excluded middle
as decidable identity), and so do the *prima via* premises and act's simple
priority; the only first mover moved by none is the maximal being `m`, but `y`,
which does not cause `m`'s being, is simply prior to it. -/
theorem withoutPriorIsCauseNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect) (God : Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      MaximeEnsIsGod InAct MoreIn esse God →
      CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God →
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The *Metaphysics* II premise is needed. In `MutualPriority` with `causesBoth`,
where `y` also causes `m`'s being, every other premise of `firstMoverIsFirstBeing`
holds (with `m` as God; excluded middle as decidable identity), and so do the
*prima via* premises and act's simple priority; but `y`, a cause of `m`'s being
that is not more a being than `m`, is simply prior to the maximal being. -/
theorem withoutCauseMoreNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect) (God : Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      MaximeEnsIsGod InAct MoreIn esse God →
      CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God →
      SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The premises of the #147 results (`quartaVia`, `firstMoverIsMaximeEns`,
`firstMoverIsFirstBeing`, `oneFirstMoverViaMaximeEns` and
`firstMoverHasPerfectionsOfThings`), the seven *prima via* premises (#151) and act's
simple priority (#166) hold together in one finite model, with excluded middle
as decidable identity. The model also has a God and a caused agent that moves and
is moved, so the q.105 a.5 premise does not hold only vacuously. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect) (God : Being → Prop),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      GradesFoundInThingsReading MoreIn bonum verum nobile ∧
      GradesByApproachToAMaximumReading InAct MoreIn ∧
      MostTrueIsMostBeingReading InAct MoreIn verum esse ∧
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      ActualityOnlyInsofarAsBeingReading InAct esse ∧
      MaximeEnsIsGod InAct MoreIn esse God ∧
      CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God ∧
      SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse ∧
      CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
      PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse ∧
      (∀ a b : Being, a = b ∨ a ≠ b) ∧
      (∃ y x, MovesAsMoved y x) ∧
      (∃ g a x r r', God g ∧ a ≠ g ∧ CausesIn g a esse ∧ MovesIn a x r ∧
        MovedIn a r') := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
