module
public import TruthCore.Metaethics.GoodnessCorrectSupport
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCorrectSupport.Elimination
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
theorem dueFromSupportedElimination (f : Frame) (s : DefinitionSpace f)
    (hSupport : CorrectAccountSupport s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  sorry
end TruthCore.Results.Metaethics.GoodnessCorrectSupport.Elimination
