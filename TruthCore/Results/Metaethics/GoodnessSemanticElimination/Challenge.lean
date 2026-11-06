import TruthCore.Metaethics.GoodnessFormEnd

namespace TruthCore.Results.Metaethics.GoodnessSemanticElimination
open TruthCore.Metaethics.GoodnessFormEnd

/-- Uses weak semantic coverage; a renamed/coextensive proposal creates no gap. -/
theorem dueFromSemanticElimination (f : Frame) (s : DefinitionSpace f)
    (hCoverage : SemanticNamedCoverage s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  sorry
end TruthCore.Results.Metaethics.GoodnessSemanticElimination
