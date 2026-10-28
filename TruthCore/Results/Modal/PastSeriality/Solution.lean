import TruthCore.Modal.PastSerialityCertificate
import TruthCore.Results.Modal.StandardCorrespondence.Solution
namespace TruthCore.Results.Modal.PastSeriality
open TruthCore.Modal
open TruthCore.Modal.PastSeriality
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem strictPast_serial_iff {T : Type} [Preorder T] (now : T) :
    Serial (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) ↔ PastIsInfinite (fun s t : T => s < t) now := by
  constructor
  · intro h t ht
    obtain ⟨s, hs⟩ := h ⟨t, ht⟩
    exact ⟨s.val, hs⟩
  · intro h t
    obtain ⟨s, hs⟩ := h t.val t.property
    have hBeforeNow : s < now := by
      rcases t.property with heq | hlt
      · exact lt_of_lt_of_eq hs heq
      · exact lt_trans hs hlt
    exact ⟨⟨s, Or.inr hBeforeNow⟩, hs⟩

theorem strictPast_D_iff {T : Type} [Preorder T] (now : T) :
    Valid (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ PastIsInfinite (fun s t : T => s < t) now := by
  exact (TruthCore.Results.Modal.StandardCorrespondence.d_iff_serial _).trans
    (strictPast_serial_iff now)

theorem inclusivePast_T_D {T : Type} [Preorder T] :
    Reflexive (⟨fun t s : T => s ≤ t⟩ : Frame T) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.atom ())) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.diamond (.atom ()))) := by
  have hReflexive : Reflexive (⟨fun t s : T => s ≤ t⟩ : Frame T) :=
    fun _ => le_rfl
  exact ⟨hReflexive, axiomT_valid _ hReflexive (.atom ()),
    axiomD_valid _ (reflexive_implies_serial _ hReflexive) (.atom ())⟩

theorem checks : PastSerialityCertificate := by
  refine ⟨fun _ _ now => strictPast_serial_iff now,
    fun _ _ now => strictPast_D_iff now,
    fun _ _ => inclusivePast_T_D, ?_⟩
  have hNotInfinite : ¬ PastIsInfinite (fun s t : Nat => s < t) 0 := by
    intro h
    obtain ⟨t, ht⟩ := h 0 (Or.inl rfl)
    exact Nat.not_lt_zero t ht
  refine ⟨⟨0, Or.inl rfl, fun t ht => Nat.not_lt_zero t ht⟩,
    hNotInfinite, ?_, ?_⟩
  · intro h
    obtain ⟨t, ht⟩ := h ⟨0, Or.inl rfl⟩
    exact Nat.not_lt_zero t.val ht
  · exact reflexive_implies_serial _ (fun n => Nat.le_refl n)
end TruthCore.Results.Modal.PastSeriality
