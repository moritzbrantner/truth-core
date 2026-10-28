import TruthCore.Causality.FiniteNecessaryUnion

namespace TruthCore.Results.Causality.FiniteNecessaryUnion.Classification

open TruthCore.Causality.FiniteNecessaryUnion
open TruthCore.German.Kant.CosmologicalInference

/-- Finite nonempty necessary carriers have a union source or nonempty TransGen loop, inclusively. If no source exists and no loop existed, Mathlib finite transitive irreflexive well-foundedness would yield a source by induction. Finiteness and population remain explicit open background; no root discharge. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (h : FinitePopulation m w₀) : SourceOrCycle m s w₀ := by
  exact source_or_cycle m s w₀ h

end TruthCore.Results.Causality.FiniteNecessaryUnion.Classification
