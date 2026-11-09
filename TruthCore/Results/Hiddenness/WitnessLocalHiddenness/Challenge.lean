import TruthCore.Hiddenness.WitnessLocalHiddenness
import TruthCore.Results.Hiddenness.ActualRoot.Solution

namespace TruthCore.Results.Hiddenness.WitnessLocalHiddenness
open TruthCore.Hiddenness TruthCore.Hiddenness.ActualRoot
open TruthCore.Hiddenness.WitnessLocalHiddenness

theorem openWeakens (s : Sig) (h : ActualAlwaysOpen s) : WitnessOpen s := by
  sorry

theorem accessWeakens (s : Sig) (h : ActualAccessNeedsBelief s) : WitnessAccess s := by
  sorry

theorem selectWitness (s : Sig) (ho : WitnessOpen s) (ha : WitnessAccess s)
    (hn : NonresistantNonbelief s) : SelectedBundle s := by
  sorry

theorem noGod (s : Sig) (hl : ActualGodLoves s) (hs : SelectedBundle s) : NoGod s := by
  sorry

theorem noRouteGod {B : Type} (IsGod : B → Prop) (s : Sig)
    (hl : ActualGodLoves s) (hs : SelectedBundle s)
    (hi : RouteIdentification IsGod s) : NoRouteGod IsGod := by
  sorry

theorem guardEquivalent (s : Sig) (hn : NonresistantNonbelief s) :
    (GuardedLove s ↔ ActualGodLoves s) := by
  sorry

theorem controls : TruthCore.Hiddenness.WitnessLocalHiddenness.Controls := by
  sorry
end TruthCore.Results.Hiddenness.WitnessLocalHiddenness
