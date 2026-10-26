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
    constructor
    · intro _
      rfl
    · intro _
      trivial
  · refine ⟨fun _ => false, ?_⟩
    intro x w
    constructor
    · intro h
      cases h
    · intro h
      cases h
  · intro Φ ⟨f, hf⟩
    refine ⟨fun b => ! f b, ?_⟩
    intro x w
    change (¬ Φ x w) ↔ ((!f (atom x w)) = true)
    constructor
    · intro hNot
      cases hBit : f (atom x w) with
      | false => rfl
      | true => exact False.elim (hNot ((hf x w).mpr hBit))
    · intro hNotBit hProperty
      have hBit := (hf x w).mp hProperty
      rw [hBit] at hNotBit
      cases hNotBit
  · intro Φ Ψ ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨fun b => f b && g b, ?_⟩
    intro x w
    change (Φ x w ∧ Ψ x w) ↔ ((f (atom x w) && g (atom x w)) = true)
    constructor
    · rintro ⟨hΦ, hΨ⟩
      have hF := (hf x w).mp hΦ
      have hG := (hg x w).mp hΨ
      rw [hF, hG]
      rfl
    · intro hBoth
      cases hF : f (atom x w) <;> cases hG : g (atom x w)
      · rw [hF, hG] at hBoth
        cases hBoth
      · rw [hF, hG] at hBoth
        cases hBoth
      · rw [hF, hG] at hBoth
        cases hBoth
      · exact ⟨(hf x w).mpr hF, (hg x w).mpr hG⟩

end TruthCore.Results.Isabelle.GoedelGod.BooleanFragmentClosed
