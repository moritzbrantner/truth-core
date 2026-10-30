import TruthCore.Modal.PastSerialityCertificate
namespace TruthCore.Results.Modal.PastSeriality
open TruthCore.Modal
open TruthCore.Modal.PastSeriality
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem strictPast_serial_iff {T : Type} [Preorder T] (now : T) :
    Serial (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) ↔ PastIsInfinite (fun s t : T => s < t) now := by sorry

theorem strictPast_D_iff {T : Type} [Preorder T] (now : T) :
    Valid (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ PastIsInfinite (fun s t : T => s < t) now := by sorry

theorem inclusivePast_T_D {T : Type} [Preorder T] :
    Reflexive (⟨fun t s : T => s ≤ t⟩ : Frame T) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.atom ())) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.diamond (.atom ()))) := by sorry

theorem checks : PastSerialityCertificate := by sorry
end TruthCore.Results.Modal.PastSeriality
