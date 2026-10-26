import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskOscillation
open TruthCore.Causality

/-- A candidate terminal value disagrees with either the stage at the
claimed cutoff or its immediate successor. -/
theorem supertaskOscillation : AlternatingOutputHasNoStableLimit := by
  intro terminal hStable
  obtain ⟨cutoff, hAfter⟩ := hStable
  have hFirst := hAfter cutoff (Nat.le_refl cutoff)
  have hNext := hAfter (cutoff + 1) (Nat.le_succ cutoff)
  have hToggle : AlternatingStageOutput (cutoff + 1) =
      !AlternatingStageOutput cutoff := rfl
  rw [hNext, hFirst] at hToggle
  cases terminal <;> simp at hToggle

end TruthCore.Results.Causality.SupertaskOscillation
