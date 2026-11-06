module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentFailure
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem absentFailure {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (h : OnlyAbsentCausers o F w) : WholeCauserActualityFails o F w := by
  intro hActual
  obtain ⟨c, hc⟩ := h.1
  exact h.2 ⟨c, hActual c hc, hc⟩

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentFailure
