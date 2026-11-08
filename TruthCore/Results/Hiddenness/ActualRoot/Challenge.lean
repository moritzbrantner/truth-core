import TruthCore.Hiddenness.ActualRoot
import TruthCore.Results.Hiddenness.PremisesIndependent.Solution
import TruthCore.Results.Hiddenness.NontheisticConsistent.Solution

namespace TruthCore.Results.Hiddenness.ActualRoot
open TruthCore.Hiddenness TruthCore.Hiddenness.ActualRoot

theorem loveWeakens (s : Sig) (h : GodLoves s) : ActualGodLoves s := by
  sorry

theorem openWeakens (s : Sig) (h : AlwaysOpen s) : ActualAlwaysOpen s := by
  sorry

theorem beliefWeakens (s : Sig) (h : AccessNeedsBelief s) : ActualAccessNeedsBelief s := by
  sorry

theorem noGod (s : Sig) (hLove : ActualGodLoves s) (hOpen : ActualAlwaysOpen s)
    (hBelief : ActualAccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s) : NoGod s := by
  sorry

theorem noRouteGod {B : Type} (IsGod : B → Prop) (s : Sig)
    (hLove : ActualGodLoves s) (hOpen : ActualAlwaysOpen s)
    (hBelief : ActualAccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s)
    (hIdentification : RouteIdentification IsGod s) : NoRouteGod IsGod := by
  sorry

theorem controls : Controls := by
  sorry
end TruthCore.Results.Hiddenness.ActualRoot
