module

public import TruthCore.Alternatives.ReligiousLanguageSemantics
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Difference.Solution
public import TruthCore.Results.Alternatives.ReligiousLanguageSemantics.Uniform.Solution

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem matchedDifferenceRejectsCrossDiscourse (P : Profile) (h : MatchedReligiousTruthDifference P) : CrossDiscourseFaceValueRejected P := by
  intro hc
  exact matchedDifferenceRejectsUniform P h (crossDiscourseSuppliesUniform P hc)

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
