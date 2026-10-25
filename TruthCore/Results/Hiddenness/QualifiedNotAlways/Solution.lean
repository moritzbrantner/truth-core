import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.QualifiedNotAlways
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem qualifiedNotAlways : QualifiedDoesNotForceAlways := by
  refine ⟨delayedModel, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro _ _
    rfl
  · intro _ _ _ t _ _ hNoReason
    cases t with
    | false => exact (hNoReason rfl).elim
    | true => exact Or.inl rfl
  · intro _ _ t hNoBelief hAccess
    exact hNoBelief hAccess
  · intro _ _ _ t _ _ hNoAccess
    cases t with
    | false => rfl
    | true => exact (hNoAccess (Or.inl rfl)).elim
  · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩
  · intro hOpen
    have h := hOpen () rfl () false trivial (fun h => h)
    exact h.elim Bool.false_ne_true Bool.false_ne_true

end TruthCore.Results.Hiddenness.QualifiedNotAlways
