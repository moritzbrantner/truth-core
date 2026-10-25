import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.NontheisticDevelopmentConsistent
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem nontheisticDevelopmentConsistent : NontheisticDevelopmentConsistent := by
  refine ⟨nontheisticModel, ?_⟩
  unfold NontheisticDevelopment
  refine ⟨Bool.false_ne_true, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ h
    exact h
  · intro _ h
    exact (Bool.false_ne_true h).elim
  · intro _ _ _ _ hAccess
    exact hAccess
  · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩

  · intro _ _ _ hNoConcept hBelief
    exact hNoConcept hBelief
  · intro _ _ hNoBelief
    exact Or.inl hNoBelief

end TruthCore.Results.Hiddenness.NontheisticDevelopmentConsistent
