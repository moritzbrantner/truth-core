import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
import TruthCore.Results.Causality.SameRespectActualization.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem primaViaRelative {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveAsMovedInRelevantRespectReading
      MovedIn MovesIn MovesAsMoved RelevantTo)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    RelativelyUnmovedMoverCannotBeLackingReading MovedIn MovesIn RelevantTo := by
  -- Reuse the two separately checked first-way intermediate inferences.
  have hNoSelf := TruthCore.Results.Causality.SameRespectActualization.noSelfMotion
    MovedIn MovesIn InPotency InAct hPotency hAct hNotBoth
  have hAnother := TruthCore.Results.Causality.SameRespectActualization.movedByAnother
    MovedIn MovesIn hReduction hNoSelf
  -- INF-AQUINAS-ST-I-Q2-A3-RELATIVE-FIRST-MOVER
  intro hNoFirst
  have hNoMotion : ∀ x, (∃ r, MovedIn x r) → False := by
    intro x
    have hAcc := hRegress x
    induction hAcc with
    | intro x _ ih =>
      intro ⟨r, hMoved⟩
      obtain ⟨y, hDistinct, hMoves⟩ := hAnother x r hMoved
      -- If y were moved in no respect relevant to moving x, it would be a
      -- relatively first mover.
      have hRelevantlyMoved : ¬ ¬ ∃ r', MovedIn y r' ∧ RelevantTo y x r r' := by
        intro hUnmoved
        exact hNoFirst ⟨y, x, r, hMoves, fun r' h => hUnmoved ⟨r', h⟩⟩
      exact hRelevantlyMoved fun ⟨r', hMoved', hRelevant⟩ =>
        ih y (hPerSe y x r r' hDistinct hMoves hMoved' hRelevant) ⟨r', hMoved'⟩
  obtain ⟨x, r, hMoved⟩ := hSense
  exact hNoMotion x ⟨r, hMoved⟩
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
