module

public import TruthCore.Comparison.Hiddenness
public import TruthCore.Hiddenness.Models

@[expose] public section

namespace TruthCore.Results.Hiddenness.NontheisticConsistent
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem nontheisticConsistent : NontheisticConsistent := by
  refine ⟨nontheisticModel, ?_⟩
  unfold Nontheistic
  refine ⟨Bool.false_ne_true, ?_, ?_, ?_, ?_⟩
  · intro _ h
    exact h
  · intro _ h
    exact (Bool.false_ne_true h).elim
  · intro _ _ _ _ hAccess
    exact hAccess
  · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩


end TruthCore.Results.Hiddenness.NontheisticConsistent
