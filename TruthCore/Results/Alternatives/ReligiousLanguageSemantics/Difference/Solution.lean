module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem matchedDifferenceRejectsUniform (P : Profile) (h : MatchedReligiousTruthDifference P) : MatchedTruthUniformRejected P := by
  obtain ⟨s, hr, hc0, hc1, hd⟩ := h
  intro hu
  cases hd with
  | inl hd => exact hd.2 ((hu s hr hc0 hc1).1 hd.1)
  | inr hd => exact hd.2 ((hu s hr hc0 hc1).2 hd.1)

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
