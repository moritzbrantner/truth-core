import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover
  FirstUnmovedMoverIsFirstBeing)
/-- ST I q.3 a.1 co., second proof, for the *prima via*'s mover: if the first
mover moved by none is the first being (open bridge), then, since the first
being is in no way in potency, every first mover moved by none is pure act. Discharges the #159 gap
statement `FirstUnmovedMoverIsPureAct` with `PureAct InPotency` for its
`PureAct` parameter. -/
theorem firstMoverPureAct {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hFirstBeing : FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  sorry

/-- The *prima via*'s premises (#151) together with the act-priority premise do
not yield pure act. In the model, `f` heats `x` and is moved by nothing, yet it is
in potency to cold, a respect in which it moves nothing; `z`, in act as to cold,
is simply prior to `f`. So `FirstUnmovedMoverIsFirstBeing` is not
redundant: "moved by none" does not mean "in potency in no respect". -/
theorem firstWayDoesNotYieldPureAct :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved : Being → Being → Prop)
      (PriorSimply : Being → Being → Prop),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      FirstUnmovedMoverIsPureAct MovedIn MovesIn (PureAct InPotency) := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct
