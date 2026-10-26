import TruthCore.Isabelle.AFP.GoedelGod.GeneratedFragment

namespace TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed

open TruthCore.Isabelle.AFP.GoedelGod

theorem checks {World Ind : Type} : BooleanFragmentClosed World Ind := by
  intro atom
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨id, ?_⟩
    intro x w
    rfl
  · refine ⟨fun _ => true, ?_⟩
    intro x w
    simp
  · refine ⟨fun _ => false, ?_⟩
    intro x w
    simp
  · intro Φ ⟨f, hf⟩
    refine ⟨fun b => ! f b, ?_⟩
    intro x w
    change (¬ Φ x w) ↔ ((!f (atom x w)) = true)
    rw [hf x w]
    cases f (atom x w) <;> simp
  · intro Φ Ψ ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨fun b => f b && g b, ?_⟩
    intro x w
    change (Φ x w ∧ Ψ x w) ↔ ((f (atom x w) && g (atom x w)) = true)
    rw [hf x w, hg x w]
    cases f (atom x w) <;> cases g (atom x w) <;> simp

end TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed
