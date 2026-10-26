import TruthCore.Greek.Plato.Theaetetus
namespace TruthCore.Results.Plato.Theaetetus.PeritropeModels
open TruthCore.Logic.SelfApplication
open TruthCore.Greek.Plato.Theaetetus
/-- Two Boolean models. Exemption: contents are Booleans with Boolean negation,
the thesis is `true`, agent `true` holds it and agent `false` denies it; only
`true` is in scope and only `true` is absolutely true, so the unqualified
doctrine holds once the denial is exempted. Relative: each agent's relative
truth is what seems to it, agent `true` holds the thesis, agent `false` its
denial, and nothing is absolutely true. Consistency, not a defense. -/
theorem peritropeModels : PeritropeModels := by
  constructor
  · refine ⟨fun x p => p = x, ⟨fun p => p = true, fun _ _ => True⟩, Bool.not,
      fun p => p = true, true, true, ?_, rfl, ⟨false, rfl⟩, ?_, rfl, ?_⟩
    · intro p hScope _
      exact hScope
    · intro p hNeg hTrue
      rw [hTrue] at hNeg
      cases hNeg
    · intro h
      cases h
  · refine ⟨fun x p => p = x, ⟨fun _ => False, fun x p => p = x⟩, Bool.not, true, true,
      ?_, ?_, rfl, ⟨false, rfl⟩, ?_, ?_⟩
    · intro x p h
      exact h
    · intro x p hNeg hTrue
      rw [hTrue] at hNeg
      cases x <;> cases hNeg
    · intro p hNeg _
      exact hNeg
    · intro p h
      exact h
end TruthCore.Results.Plato.Theaetetus.PeritropeModels
