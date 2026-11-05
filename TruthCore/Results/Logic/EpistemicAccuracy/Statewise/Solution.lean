module

public import TruthCore.Logic.EpistemicAccuracy

@[expose] public section
namespace TruthCore.Results.Logic.EpistemicAccuracy.Statewise
open TruthCore.Logic.EpistemicAccuracy

theorem dominance : DominanceCertificate := by
  intro r s hr0 hr1 hs0 hs1
  have hid : ∀ truth, pairError truth r s -
      pairError truth (projectFirst r s) (projectSecond r s) = (r+s-1)^2/2 := by
    intro truth
    cases truth <;> simp only [pairError, Bool.false_eq_true, ↓reduceIte,
      projectFirst, projectSecond] <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hid, ?_⟩
  · dsimp [projectFirst]; linarith
  · dsimp [projectFirst]; linarith
  · dsimp [projectSecond]; linarith
  · dsimp [projectSecond]; linarith
  · dsimp [projectFirst, projectSecond]; ring
  · intro hne truth
    have hsq : 0 < (r+s-1)^2 := sq_pos_of_ne_zero (by intro h; apply hne; linarith)
    have := hid truth
    linarith
end TruthCore.Results.Logic.EpistemicAccuracy.Statewise
