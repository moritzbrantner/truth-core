import TruthCore.Hiddenness.Vocabulary

namespace TruthCore.Results.Hiddenness.GapHasDevelopmentalAccount
open TruthCore.Hiddenness

theorem gapHasDevelopmentalAccount {s : Sig} (hAccount : DevelopmentalAccount s) (hGap : NonresistantNonbelief s) : GapHasDevelopmentalAccount s := by
  obtain ⟨p, t, hCap, hNonresistant, hLacks⟩ := hGap
  have hMechanism := hAccount p t hLacks
  exact ⟨p, t, hCap, hNonresistant, hLacks, hMechanism⟩

end TruthCore.Results.Hiddenness.GapHasDevelopmentalAccount
