import TruthCore.Logic.Relativism
namespace TruthCore.Results.Logic.Relativism.Models
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
/-- Two models. Horn 2: nothing is absolutely true, the thesis `true` is in its
own scope and disquotes, and it is true for agent `true` only. Exemption: the
scope is `{false}`, only `true` is absolutely true, and the thesis `true` is
asserted absolutely without contradiction. Consistency, not a defense. -/
theorem noAbsoluteTruthModels : NoAbsoluteTruthModels := by
  constructor
  · refine ⟨⟨fun _ => False, fun a _ => a = true⟩, fun _ => True, true, true,
      ?_, trivial, ?_, rfl, ?_⟩
    · intro p _ hTrue
      exact hTrue
    · intro hTrue
      exact hTrue.elim
    · intro h
      cases h
  · refine ⟨⟨fun p => p = true, fun _ _ => False⟩, fun p => p = false, true, ?_, ?_, ?_, rfl⟩
    · intro p hScope hTrue
      rw [hScope] at hTrue
      cases hTrue
    · intro h
      cases h
    · intro _ p hScope hTrue
      rw [hScope] at hTrue
      cases hTrue
end TruthCore.Results.Logic.Relativism.Models
