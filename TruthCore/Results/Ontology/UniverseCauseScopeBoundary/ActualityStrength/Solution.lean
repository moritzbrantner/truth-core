module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.ActualityStrength
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem actualityStrength {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (h : TruthCore.Causality.ActualFusionNecessaryBeing.CausesHaveActualEndpointsAt o w) :
    WholeCausersExist o F w := by
  exact fun c hc => (h c F.whole hc).1

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.ActualityStrength
