import TruthCore.Causality.FiniteNecessaryUnion

namespace TruthCore.Results.Causality.FiniteNecessaryUnion.LocalWitness

open TruthCore.Causality.FiniteNecessaryUnion
open TruthCore.German.Kant.CosmologicalInference

/-- Under worldwise acyclicity restricted to the same necessary subtype, no nonempty union loop has all its edges witnessed in a single world. Map any proposed common-world path to the local relation and contradict its acyclicity. No claim about all causation or contingent individuals. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (h : LocallyAcyclic m s w₀) : NoSingleWorldCycle m s w₀ := by
  sorry

end TruthCore.Results.Causality.FiniteNecessaryUnion.LocalWitness
