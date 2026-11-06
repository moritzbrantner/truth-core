import TruthCore.Logic.ExcludedMiddleAssertionBoundary
namespace TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.ExactPolicyRival
open TruthCore.Logic
open TruthCore.Logic.ExcludedMiddleAssertionBoundary
theorem exactPolicyRival {Stage : Type} (Proved Asserts : Stage → Prop → Prop)
    (h : ExcludedMiddleWithheld Proved Asserts) : NotAllInstancesAsserted Asserts := by
  sorry
end TruthCore.Results.Logic.ExcludedMiddleAssertionBoundary.ExactPolicyRival
