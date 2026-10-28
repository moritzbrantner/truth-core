import TruthCore.Explanation.ConservativeReasonExpansion

namespace TruthCore.Results.Explanation.ConservativeReasonExpansion

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.ExistencePSR
open TruthCore.Modal.WorldwiseExplanation
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Explanation.ConservativeReasonExpansion

theorem canonicalCoverage (o : Ontic W B) :
    CoverageAndGuardedStability (canonical o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w x r h
    exact h.2
  · intro w x hx
    exact ⟨.intrinsic x, rfl, hx⟩
  · intro x
    exact ⟨.intrinsic x, fun _ hx => ⟨rfl, hx⟩⟩
  · intro x w v r h hx
    exact ⟨h.1, hx⟩

/-- A universal validity over these enriched models is precisely universal
validity over the original ontology class. The weak enrichment imposes no
additional condition on any underlying causal relation. -/
theorem onticPropertyConservative (P : Ontic W B → Prop) :
    (∀ m : Model W B, CoverageAndGuardedStability m → P m.ontic) ↔
      ∀ o : Ontic W B, P o := by
  constructor
  · intro h o
    exact h (canonical o) (canonicalCoverage o)
  · intro h m _
    exact h m.ontic

theorem checks : Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W B o
    exact ⟨canonical o, rfl, canonicalCoverage o⟩
  · intro W B P
    exact onticPropertyConservative P
  · refine ⟨canonical fixedEffects, rfl, canonicalCoverage fixedEffects,
      fixedEffectsSound, fixedSourceNecessaryAt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v _
      exact Or.inr rfl
    · exact ⟨rfl, Or.inr rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · intro h
      cases h
    · exact ⟨rfl, rfl⟩
  · refine ⟨canonical alternatingEffects, rfl,
      canonicalCoverage alternatingEffects, effectsSound,
      firstEffectContingent, ?_, ?_⟩
    · exact ⟨rfl, Or.inr rfl⟩
    · intro h
      rcases h.2 with h | h
      · cases h
      · cases h

end TruthCore.Results.Explanation.ConservativeReasonExpansion
