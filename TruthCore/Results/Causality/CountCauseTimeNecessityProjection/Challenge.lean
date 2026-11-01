import TruthCore.Causality.CountCauseTimeNecessity

namespace TruthCore.Results.Causality.CountCauseTimeNecessityProjection
open TruthCore.Causality.CountCauseTimeNecessity
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference

/-- Assembly projection: retain the SAME actual necessary individual while
forgetting its concrete guard and accessible-world causal role. -/
theorem project {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hWitness : NecessaryConcreteCauseAt h Concrete CauseCount w) :
    NecessaryBeing h.ontic w := by
  sorry

end TruthCore.Results.Causality.CountCauseTimeNecessityProjection
