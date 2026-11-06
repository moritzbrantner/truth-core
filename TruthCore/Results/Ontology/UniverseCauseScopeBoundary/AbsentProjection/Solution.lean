module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentProjection
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem absentProjection {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (h : OnlyAbsentCausers o F w) : NoExistingCause o F w := by
  exact h.2

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentProjection
