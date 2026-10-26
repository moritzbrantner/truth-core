import TruthCore.Causality.GroundingRegress

namespace TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
open TruthCore.Causality.GroundingRegress
open TruthCore.German.Kant.CosmologicalInference

/-- Suppose every existing being is contingent. By well-founded induction on
the world's causal relation, no being exists: an existing being would be
contingent, so by the local causal principle it would have an existing cause,
which by the induction hypothesis does not exist. This contradicts the given
existent. No classical logic and no axiom is used. -/
theorem wellFoundedCausesBlockAllContingent : WellFoundedCausesBlockAllContingent := by
  intro World Entity m w hLocal hWF ⟨x, hx⟩ hAll
  have noneExists : ∀ z, ¬ m.ExistsAt w z := by
    intro z
    induction hWF.apply z with
    | intro z _ ih =>
      intro hz
      obtain ⟨y, hy, hCauses, _⟩ := hLocal w z (hAll z hz)
      exact ih y hCauses hy
  exact noneExists x hx

end TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
