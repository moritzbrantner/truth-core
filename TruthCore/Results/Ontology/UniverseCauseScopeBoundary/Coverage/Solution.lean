module

public import TruthCore.Ontology.UniverseCauseScopeBoundary

@[expose] public section
namespace TruthCore.Results.Ontology.UniverseCauseScopeBoundary.Coverage
open TruthCore.Ontology.UniverseCauseScopeBoundary
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference

/-- Analyst scope obligation; existing causal predicates and source meanings stay fixed. -/
theorem coverage {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (hEM : TruthCore.Logic.ExcludedMiddle) : CauseScopeTrilemma o F w := by
  cases hEM (UniverseHasExistingCause o F w) with
  | inl h => exact Or.inl h
  | inr hn =>
    cases hEM (HasSomeCause o F w) with
    | inl h => exact Or.inr (Or.inr ⟨h, hn⟩)
    | inr h => exact Or.inr (Or.inl (fun c hc => h ⟨c, hc⟩))

end TruthCore.Results.Ontology.UniverseCauseScopeBoundary.Coverage
