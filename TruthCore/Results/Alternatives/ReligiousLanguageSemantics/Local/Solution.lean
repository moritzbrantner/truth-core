module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem crossDiscourseSuppliesLocal (P : Profile) (h : CrossDiscourseFaceValue P) : LocalFaceValue P := by
  exact h.1

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
