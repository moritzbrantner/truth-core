module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.UncausedStrength
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem uncausedStrength {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (h : UniverseUncaused o F w) : NoExistingCause o F w := by
  rintro ⟨c, _, hc⟩
  exact h c hc

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.UncausedStrength
