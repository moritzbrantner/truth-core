import TruthCore.Hiddenness.Vocabulary

namespace TruthCore.Results.Hiddenness.GapHasReason
open TruthCore.Hiddenness

theorem gapHasReason {s : Sig} (hGod : GodExists s) (hBelief : AccessNeedsBelief s) (hReason : ReasonForEachGap s) (hGap : NonresistantNonbelief s) : GapHasReason s := by
  obtain ⟨p, t, hCap, hNonresistant, hLacks⟩ := hGap
  have hNoAccess := hBelief s.actual p t hLacks
  have hSufficient := hReason s.actual hGod p t hCap hNonresistant hNoAccess
  exact ⟨p, t, hCap, hNonresistant, hLacks, hSufficient⟩

end TruthCore.Results.Hiddenness.GapHasReason
