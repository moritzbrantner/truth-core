import TruthCore.Causality.GroundingRegress

namespace TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
open TruthCore.Causality.GroundingRegress
open TruthCore.German.Kant.CosmologicalInference

/-- The induction only needs dependence at the selected world, and does not
need the original global principle's additional distinctness clause. This
local form lets later typed restrictions reuse the verified regress proof. -/
theorem wellFoundedCausesBlockAllContingentAt
    {World Entity : Type} (m : Ontic World Entity) (w : World)
    (hLocal : ∀ x, ContingentAt m w x →
      ∃ y, m.ExistsAt w y ∧ m.Causes w y x)
    (hWF : WellFounded (m.Causes w))
    (hPop : ∃ x, m.ExistsAt w x) :
    ¬ ∀ x, m.ExistsAt w x → ContingentAt m w x := by
  obtain ⟨x, hx⟩ := hPop
  intro hAll
  have noneExists : ∀ z, ¬ m.ExistsAt w z := by
    intro z
    induction hWF.apply z with
    | intro z _ ih =>
      intro hz
      obtain ⟨y, hy, hCauses⟩ := hLocal z (hAll z hz)
      exact ih y hCauses hy
  exact noneExists x hx

/-- Original Kantian result, now factoring the already-proved induction into
its actual-world form. It remains constructive and its public type is fixed. -/
theorem wellFoundedCausesBlockAllContingent : WellFoundedCausesBlockAllContingent := by
  intro World Entity m w hLocal hWF hPop
  exact wellFoundedCausesBlockAllContingentAt m w
    (fun x hx => by
      obtain ⟨y, hy, hCauses, _⟩ := hLocal w x hx
      exact ⟨y, hy, hCauses⟩) hWF hPop

end TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent
