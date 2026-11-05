module
public import TruthCore.Results.Explanation.TruthmakerTheories.Solution
@[expose] public section
namespace TruthCore.Results.Explanation.TruthmakerTheories
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.Explanation.TruthmakerTheories

theorem truthSetMap : TruthSetMap := by
  have hs : Sound truthSetArena truthSetMaking :=
    ⟨fun _ _ _ h => h.2, fun _ _ _ h => h.1⟩
  have hn := TruthCore.Results.Explanation.DisjunctionGround.truthmakers_facts.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨hs, fun w p _ hp => ⟨w, rfl, hp⟩⟩, ?_, fun _ _ => Iff.rfl,
    ?_, ?_, fun _ _ => trivial, fun v _ => ⟨v, rfl, trivial⟩, ?_, hn⟩
  · rintro w b p ⟨hb, hp⟩ v _ hv
    have hwv : w = v := hb.symm.trans hv
    exact hwv ▸ hp
  · intro p; exact ⟨fun w => ¬ p w, fun _ => Iff.rfl⟩
  · intro p q; exact ⟨fun w => p w ∧ q w, fun _ => Iff.rfl⟩
  · intro hu
    exact hn (uniformNecessary truthSetArena truthSetMaking false (fun _ => True) hs.2 trivial hu)
end TruthCore.Results.Explanation.TruthmakerTheories
