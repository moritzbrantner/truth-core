module
public import TruthCore.Metaethics.GoodnessCorrectSupport
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCorrectSupport.Strength
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
theorem globalCoverageImpliesSupport (f : Frame) (s : DefinitionSpace f)
    (hCoverage : SemanticNamedCoverage s) : CorrectAccountSupport s := by
  intro ⟨d, hAdmissible, hCorrect⟩
  exact ⟨d, hAdmissible, hCorrect, hCoverage d hAdmissible⟩
end TruthCore.Results.Metaethics.GoodnessCorrectSupport.Strength
