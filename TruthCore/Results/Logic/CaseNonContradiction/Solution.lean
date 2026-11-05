import TruthCore.Logic.CaseNonContradiction
import TruthCore.Results.Logic.TruthPilot.LogicalFloor.Solution
namespace TruthCore.Results.Logic.CaseNonContradiction
open TruthCore.Logic.CaseNonContradiction
universe u v
/-- No being both has and lacks a case predicate in the same respect: the
dialetheic rival `SomeCasePredicateContradictionTrue` is refuted inside Lean's
logic. Relative to the F1 floor marking only (D-L, #1007). -/
theorem noCasePredicateContradiction : NoCasePredicateContradiction.{u, v} := by
  rintro ⟨_, _, P, x, r, h⟩
  -- The instance `P x r` is a proposition; reuse Lean-logic non-contradiction.
  exact TruthCore.Results.Logic.TruthPilot.LogicalFloor.nonContradiction (P x r) h
end TruthCore.Results.Logic.CaseNonContradiction
