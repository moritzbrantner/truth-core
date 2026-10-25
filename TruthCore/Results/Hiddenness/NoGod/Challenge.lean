import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.NoGod
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem noGod {s : Sig} (hLove : GodLoves s) (hOpen : AlwaysOpen s) (hBelief : AccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s) : NoGod s := by
  sorry

end TruthCore.Results.Hiddenness.NoGod
