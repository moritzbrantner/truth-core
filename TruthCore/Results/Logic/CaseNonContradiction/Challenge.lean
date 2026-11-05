import TruthCore.Logic.CaseNonContradiction
namespace TruthCore.Results.Logic.CaseNonContradiction
open TruthCore.Logic.CaseNonContradiction
universe u v
/-- No being both has and lacks a case predicate in the same respect: the
dialetheic rival `SomeCasePredicateContradictionTrue` is refuted inside Lean's
logic. Relative to the F1 floor marking only (D-L, #1007). -/
theorem noCasePredicateContradiction : NoCasePredicateContradiction.{u, v} := by
  sorry
end TruthCore.Results.Logic.CaseNonContradiction
