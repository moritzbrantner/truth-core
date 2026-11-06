module

public import TruthCore.Alternatives.ReligiousLanguageSemantics

@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousLanguageSemantics
open TruthCore.Alternatives.ReligiousLanguageSemantics

theorem localFailureRejectsNamedProfiles (P : Profile) (h : LocalFaceValueFails P) :
    NamedLocalProfilesRejected P := by
  intro hn
  cases hn with
  | inl hc => exact h hc.1
  | inr hc => exact h hc.1

end TruthCore.Results.Alternatives.ReligiousLanguageSemantics
