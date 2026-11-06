module
public import TruthCore.Metaethics.GoodnessCorrectSupport
public import TruthCore.Results.Metaethics.GoodnessSemanticElimination.Solution
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCorrectSupport.Elimination
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
theorem dueFromSupportedElimination (f : Frame) (s : DefinitionSpace f)
    (hSupport : CorrectAccountSupport s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  obtain ⟨d, _, hDescribes, hNamed⟩ := hSupport hCorrect
  apply TruthCore.Results.Metaethics.GoodnessSemanticElimination.dueFromSemanticElimination
    f (selectedSpace s d)
  · intro e he
    cases he
    exact hNamed
  · exact ⟨d, rfl, hDescribes⟩
  · exact hFeature
  · exact hApproval
end TruthCore.Results.Metaethics.GoodnessCorrectSupport.Elimination
