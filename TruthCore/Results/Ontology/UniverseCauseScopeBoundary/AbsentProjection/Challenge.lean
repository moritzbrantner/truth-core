import TruthCore.Ontology.UniverseCauseScopeBoundary

namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentProjection
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem absentProjection {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (h : OnlyAbsentCausers o F w) : NoExistingCause o F w := by
  sorry

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.AbsentProjection
