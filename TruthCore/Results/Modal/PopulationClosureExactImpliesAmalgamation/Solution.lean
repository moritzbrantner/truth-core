import TruthCore.Models.PopulationClosureSeparation

namespace TruthCore.Results.Modal.PopulationClosureExactImpliesAmalgamation
open TruthCore.Models.PopulationClosureSeparation
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
/-- Formal population-policy comparison only; no metaphysical closure defense. -/
theorem checks : ExactImpliesAmalgamation := by
  intro W I F present w h u v hu hv
  obtain ⟨z, hz, heq⟩ := h u v hu hv
  exact ⟨z, hz, fun x hx => (heq x).mp hx⟩
end TruthCore.Results.Modal.PopulationClosureExactImpliesAmalgamation
