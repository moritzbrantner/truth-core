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
  have hToggle : terminal = !terminal := by
    calc
      terminal = AlternatingStageOutput (cutoff + 1) := hNext.symm
      _ = !AlternatingStageOutput cutoff := rfl
      _ = !terminal := congrArg (fun b : Bool => !b) hFirst
  cases terminal with
  | false => exact Bool.noConfusion hToggle
  | true => exact Bool.noConfusion hToggle

end TruthCore.Results.Causality.SupertaskOscillation
