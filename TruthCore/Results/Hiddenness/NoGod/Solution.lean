module

public import TruthCore.Comparison.Hiddenness
public import TruthCore.Hiddenness.Models

@[expose] public section

namespace TruthCore.Results.Hiddenness.NoGod
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem noGod {s : Sig} (hLove : GodLoves s) (hOpen : AlwaysOpen s) (hBelief : AccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s) : NoGod s := by
  intro hGod
  obtain ⟨p, t, hCapable, hNonresistant, hLacks⟩ := hNonbelief
  have hAvailable := hOpen s.actual (hLove s.actual hGod) p t hCapable hNonresistant
  exact hBelief s.actual p t hLacks hAvailable

end TruthCore.Results.Hiddenness.NoGod
