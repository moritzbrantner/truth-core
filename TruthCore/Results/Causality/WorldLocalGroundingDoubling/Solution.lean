import TruthCore.Causality.BruteFoundationDoubling

namespace TruthCore.Results.Causality.WorldLocalGroundingDoubling

open TruthCore.Causality.BruteFoundationDoubling

/-- Composes independently checked local structure preservation lemmas into
a universal two-world model-construction theorem. No choice principle,
unrestricted PSR, philosophical necessitation or source claim is assumed. -/
theorem checks : WorldLocalGroundingDoublingSchema := by
  intro Being s noninitial hPop hWF hSound hLaw
  exact ⟨(fun _ _ => True.intro),
    doublesPopulation s hPop,
    doublesWellFounded s hWF,
    doublesGroundSound s hSound,
    doublesNoninitialCoverage s noninitial hLaw,
    doubledHasNoNecessary s⟩

end TruthCore.Results.Causality.WorldLocalGroundingDoubling
