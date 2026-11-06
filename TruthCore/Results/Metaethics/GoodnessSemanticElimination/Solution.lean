module

public import TruthCore.Metaethics.GoodnessFormEnd

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessSemanticElimination
open TruthCore.Metaethics.GoodnessFormEnd

theorem dueFromSemanticElimination (f : Frame) (s : DefinitionSpace f)
    (hCoverage : SemanticNamedCoverage s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  obtain ⟨d, hd, hDescribes⟩ := hCorrect
  rcases hCoverage d hd with hDue | hOther
  · intro x p
    exact ((hDescribes x p).trans (hDue x p)).trans (s.dueMeaning x p)
  · rcases hOther with hNatural | hAttitude
    · exact False.elim (hFeature (fun x p => (hDescribes x p).trans (hNatural x p)))
    · exact False.elim (hApproval (fun x p => (hDescribes x p).trans (hAttitude x p)))
end TruthCore.Results.Metaethics.GoodnessSemanticElimination
