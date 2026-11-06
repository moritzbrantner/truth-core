module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem crossDiscourseSuppliesUniform (P : Profile) (h : CrossDiscourseFaceValue P) : MatchedTruthUniform P := by
  exact h.2

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
