module

public import TruthCore.Logic.ExcludedMiddleAssertionBoundary

@[expose] public section
namespace TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.ExactPolicyRival
open TruthCore.Logic
open TruthCore.Logic.ExcludedMiddleAssertionBoundary
theorem exactPolicyRival {Stage : Type} (Proved Asserts : Stage → Prop → Prop)
    (h : ExcludedMiddleWithheld Proved Asserts) : NotAllInstancesAsserted Asserts := by
  intro hAll
  obtain ⟨stage, p, hNotAsserted⟩ := h.2.1
  exact hNotAsserted (hAll stage p)
end TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.ExactPolicyRival
