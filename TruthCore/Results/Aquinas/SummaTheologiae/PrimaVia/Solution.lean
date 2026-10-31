import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
import TruthCore.Results.Causality.SameRespectActualization.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem primaVia {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  -- Reuse the two separately checked first-way intermediate inferences.
  have hNoSelf := TruthCore.Results.Causality.SameRespectActualization.noSelfMotion
    MovedIn MovesIn InPotency InAct hPotency hAct hNotBoth
  have hAnother := TruthCore.Results.Causality.SameRespectActualization.movedByAnother
    MovedIn MovesIn hReduction hNoSelf
  -- INF-AQUINAS-ST-I-Q2-A3-FIRST-MOVER: reductio by well-founded induction
  intro hNoFirst
  have hNoMotion : ∀ x, (∃ r, MovedIn x r) → False := by
    intro x
    have hAcc := hRegress x
    induction hAcc with
    | intro x _ ih =>
      intro ⟨r, hMoved⟩
      obtain ⟨y, hDistinct, hMoves⟩ := hAnother x r hMoved
      -- If the mover y were moved in no respect, it would be a first mover.
      have hMoverMoved : ¬ ¬ ∃ r', MovedIn y r' := by
        intro hUnmoved
        exact hNoFirst ⟨y, ⟨x, r, hMoves⟩, fun r' h => hUnmoved ⟨r', h⟩⟩
      -- Otherwise it is a second mover, one step up a well-founded series.
      exact hMoverMoved fun hMoved' =>
        ih y (hPerSe y x r hDistinct hMoves hMoved') hMoved'
  obtain ⟨x, r, hMoved⟩ := hSense
  exact hNoMotion x ⟨r, hMoved⟩
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
