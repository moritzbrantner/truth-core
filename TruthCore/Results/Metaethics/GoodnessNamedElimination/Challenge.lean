import TruthCore.Metaethics.GoodnessFormEnd

namespace TruthCore.Results.Metaethics.GoodnessNamedElimination
open TruthCore.Logic
open TruthCore.Metaethics.GoodnessFormEnd

/-- Named coverage is an open input; no unnamed proposal is silently excluded. -/
theorem namedCoverageFork (hEM : ExcludedMiddle) : NamedCoverageFork := by
  sorry

/-- Every hypothesis is explicit, including a correct admissible account. -/
theorem dueFromNamedElimination (f : Frame) (s : DefinitionSpace f)
    (hCoverage : NamedCoverage s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  sorry
end TruthCore.Results.Metaethics.GoodnessNamedElimination
