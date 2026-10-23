import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Comparison.ProblemOfEvil.MoralGroundingAnswerMap
open TruthCore.Comparison.ProblemOfEvil
theorem moralGroundingCells :
    (∀ s, Background s → Catholic s → ExternalEvilPremise s) ∧
      (∀ s, Background s → Emotivism s → ExternalEvilPremise s → False) := by
  sorry
theorem emotivismConsistentWithBackground : ∃ s, Background s ∧ Emotivism s := by
  sorry
end TruthCore.Results.Comparison.ProblemOfEvil.MoralGroundingAnswerMap
