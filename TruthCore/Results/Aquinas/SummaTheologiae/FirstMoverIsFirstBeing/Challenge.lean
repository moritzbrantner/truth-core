import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
import TruthCore.Greek.Aristotle.Metaphysics
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (PriorAsCauseIsMoreInBeingReading)
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsFirstBeing IsFirstUnmovedMover)

/-- The first-being bridge of #166, derived through the *quarta via*. Something
`m` is maximal in being and causes the being of all others (`quartaVia`). Nothing
is simply prior to `m`, since what is simply prior is more in being
(*Metaphysics* II.1) and nothing is more in being than `m`. Every first mover
moved by none is `m` (`firstMoverIsMaximeEns`), so it is the first being. -/
theorem firstMoverIsFirstBeing {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hApplied : CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse)
    (hPriorMore : PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- Without the q.105 a.5 premise the bridge fails. In `Intelligence` every other
premise of `firstMoverIsFirstBeing` holds, with excluded middle in the only form
the proof uses (identity of beings, decidable in the model), and so do the seven
*prima via* premises and act's simple priority; but the first mover moved by none
`f` is caused by `m`, which is simply prior to it. So the *quarta via* alone does
not reach the *prima via*'s mover: an unmoved mover caused in its being is
possible unless such agents are moved to act. -/
theorem withoutAppliedAgentNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
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
      PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- Without the *Metaphysics* II premise the bridge fails. In `MutualPriority`
every other premise of `firstMoverIsFirstBeing` holds (excluded middle as
decidable identity), and so do the *prima via* premises and act's simple
priority; the only first mover moved by none is the maximal being `m`, but `y` is
simply prior to it. Being maximal in being makes a being first only if what is
simply prior is more in being. -/
theorem withoutPriorMoreNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
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
      CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  sorry

/-- The premises of the #147 results (`quartaVia`, `firstMoverIsMaximeEns`,
`firstMoverIsFirstBeing`, `oneFirstMoverViaMaximeEns` and
`firstMoverHasPerfectionsOfThings`), the seven *prima via* premises (#151) and act's
simple priority (#166) hold together in one finite model, with excluded middle
as decidable identity. The model also witnesses a per se link and a caused agent
that moves and is moved, so the q.105 a.5 premise does not hold only vacuously. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
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
      CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse ∧
      PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse ∧
      PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse ∧
      (∀ a b : Being, a = b ∨ a ≠ b) ∧
      (∃ y x, MovesAsMoved y x) ∧
      (∃ c a x r r', a ≠ c ∧ CausesIn c a esse ∧ MovesIn a x r ∧ MovedIn a r') := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
