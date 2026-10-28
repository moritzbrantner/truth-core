import TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCover.Proof

namespace TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
/-- The alternating model fails amalgamation; infinite Nat tails are populated and individually contingent with amalgamation but have neither DeRe nor finite population cover; with no successors even an empty roster satisfies cover, amalgamation and contingency without joint absence. -/
theorem checks : FiniteCoverControls := by
  exact ⟨alternating_not_amalgamation, tail_control, successor_free_control⟩
end TruthCore.Results.Case.Catholicism.StageOne.FinitePopulationCoverControls
