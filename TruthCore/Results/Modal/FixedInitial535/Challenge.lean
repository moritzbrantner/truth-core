import TruthCore.Modal.FixedInitial535

namespace TruthCore.Results.Modal.FixedInitial535
open TruthCore.Modal.FixedInitial535
open TruthCore.German.Kant.CosmologicalInference
/-- Witness propagation; this elementary implication is a transcription. -/
theorem propagate {W B D : Type} (h : History W B D) (a : W)
    (hr : Rigid h a) : ∃ b, h.initial b a ∧ NecessaryAt h.ontic a b := by
  sorry
theorem propagation : Propagation := by
  sorry
theorem controls : Controls := by
  sorry
theorem rigidBranch : RigidBranch := by
  sorry
end TruthCore.Results.Modal.FixedInitial535
