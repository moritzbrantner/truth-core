import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverHasPerfectionsOfThings
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverHasEveryPerfectionOfThings
  FirstUnmovedMoverHasEveryPerfection IsFirstUnmovedMover)

/-- ST I q.4 a.2 co., first proof, for the *prima via*'s mover. Every first mover
moved by none is the maximal being `m` of the *quarta via*. Whatever perfection
any other being has, it has being (q.4 a.1 ad 3), so `m` causes its being, and
the perfections of an effect pre-exist in its effective cause; so `m` has that
perfection too, formally or eminently. -/
theorem firstMoverHasPerfectionsOfThings {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
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
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverHasEveryPerfectionOfThings MovedIn MovesIn InAct := by
  sorry

/-- The strong bridge `FirstUnmovedMoverHasEveryPerfection` (act in *every*
respect) does not follow. In `Unhad` every premise of
`firstMoverHasPerfectionsOfThings` holds (excluded middle as decidable identity),
and so do the seven *prima via* premises and act's simple priority; but no being
is in act as to `cold`, so the first mover moved by none `m` is not either. The
first proof of q.4 a.2 reaches only the perfections found in things. -/
theorem everyRespectNotDerived :
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
      PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverHasPerfectionsOfThings
