module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem nonDescriptionRejectsLocal (P : Profile) (h : NonDescriptiveReligiousWitness P) : LocalFaceValueFails P := by
  obtain ⟨s, hr, hn⟩ := h
  intro hl
  exact hn (hl s hr).2.2.1

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
