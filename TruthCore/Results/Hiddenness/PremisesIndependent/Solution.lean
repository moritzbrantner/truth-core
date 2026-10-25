import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.PremisesIndependent
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem premisesIndependent : PremisesIndependent := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨finiteModel true false false false, ?_, ?_, ?_, rfl⟩
    · intro _ h
      exact (Bool.false_ne_true h).elim
    · intro _ _ _ hNoBelief hAccess
      exact hNoBelief hAccess
    · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩
  · refine ⟨delayedModel, ?_, ?_, ?_, rfl⟩
    · intro _ _
      rfl
    · intro _ _ _ hNoBelief hAccess
      exact hNoBelief hAccess
    · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩
  · refine ⟨finiteModel true true true false, ?_, ?_, ?_, rfl⟩
    · intro _ _
      rfl
    · intro _ _ _ _ _ _
      exact Or.inr rfl
    · exact ⟨(), false, trivial, (fun h => h), fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩
  · refine ⟨finiteModel true true true true, ?_, ?_, ?_, rfl⟩
    · intro _ _
      rfl
    · intro _ _ _ _ _ _
      exact Or.inr rfl
    · intro _ _ _ hNoBelief _
      exact hNoBelief (Or.inr rfl)

end TruthCore.Results.Hiddenness.PremisesIndependent
