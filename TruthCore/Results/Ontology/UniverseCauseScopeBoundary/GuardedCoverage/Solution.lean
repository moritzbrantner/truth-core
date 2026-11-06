module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.GuardedCoverage
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem guardedCoverage {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle) (hActual : WholeCausersExist o F w) :
    ActualCauseOrUncaused o F w := by
  cases hEM (HasSomeCause o F w) with
  | inl h =>
    obtain ⟨c, hc⟩ := h
    exact Or.inl ⟨c, hActual c hc, hc⟩
  | inr h => exact Or.inr (fun c hc => h ⟨c, hc⟩)

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.GuardedCoverage
