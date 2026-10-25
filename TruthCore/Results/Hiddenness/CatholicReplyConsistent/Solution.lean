import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.CatholicReplyConsistent
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem catholicReplyConsistent : CatholicReplyConsistent := by
  refine ⟨delayedModel, ?_⟩
  unfold CatholicReply
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _
    rfl
  · intro _ _ _ t _ _ hNoReason
    cases t with
    | false => exact (hNoReason rfl).elim
    | true => exact Or.inl rfl
  · intro _ _ _ t _ _ hNoAccess
    cases t with
    | false => rfl
    | true => exact (hNoAccess (Or.inl rfl)).elim
  · intro _ _ t hNoBelief hAccess
    exact hNoBelief hAccess
  · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩

end TruthCore.Results.Hiddenness.CatholicReplyConsistent
