module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.ExistingCause
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem existingCause {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (hCause : HasSomeCause o F w) (hActual : WholeCausersExist o F w) :
    UniverseHasExistingCause o F w := by
  obtain ⟨c, hc⟩ := hCause
  exact ⟨c, hActual c hc, hc⟩

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.ExistingCause
