module
public import TruthCore.Explanation.EmptyTruthmaker
public import TruthCore.Results.Explanation.TruthmakerTheories.Solution
@[expose] public section
namespace TruthCore.Results.Explanation.EmptyTruthmaker.Core
open TruthCore.Explanation.EmptyTruthmaker
open TruthCore.Explanation.TruthmakerTheories
 theorem incompatible (W B : Type) (F : TruthCore.Modal.Frame W)
    (present makes : W → B → Prop) (a : W)
    (hE : EmptyPossible F present a) (hT : NegativeCoverage F present makes a)
    (hI : Immanence F present makes a) : TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨w, hw, he⟩ := hE
  apply TruthCore.Results.Explanation.TruthmakerTheories.negativeMap.1
    W B Unit (arena F present) (scopedMaking F makes a) w ()
  · intro _; exact Iff.rfl
  · exact he
  · intro hn
    obtain ⟨b, hb⟩ := hT w hw hn
    exact ⟨b, hw, hb⟩
  · rintro v b _ ⟨hv, hb⟩
    exact hI v hv b hb
end TruthCore.Results.Explanation.EmptyTruthmaker.Core
