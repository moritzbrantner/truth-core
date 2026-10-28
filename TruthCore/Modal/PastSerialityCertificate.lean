import TruthCore.Modal.TemporalHistory
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

namespace TruthCore.Modal.PastSeriality
open TruthCore.Modal
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Logical assembly only: strict/inclusive past interpretations are inline
instances of the existing Frame, not metaphysical worlds or causal graphs.
No finite duration, event cardinality or physical past premise is asserted. -/
def PastSerialityCertificate : Prop :=
  (∀ (T : Type) [Preorder T] (now : T),
    Serial (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) ↔ PastIsInfinite (fun s t : T => s < t) now) ∧
  (∀ (T : Type) [Preorder T] (now : T),
    Valid (⟨fun t s : {t : T // t = now ∨ t < now} => s.val < t.val⟩ : Frame _) (.imp (.box (.atom ())) (.diamond (.atom ()))) ↔ PastIsInfinite (fun s t : T => s < t) now) ∧
  (∀ (T : Type) [Preorder T],
    Reflexive (⟨fun t s : T => s ≤ t⟩ : Frame T) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.atom ())) ∧ Valid (⟨fun t s : T => s ≤ t⟩ : Frame T) (.imp (.box (.atom ())) (.diamond (.atom ())))) ∧
  (PastIsFinite (fun s t : Nat => s < t) 0 ∧
    ¬ PastIsInfinite (fun s t : Nat => s < t) 0 ∧
    ¬ Serial (⟨fun t s : {t : Nat // t = 0 ∨ t < 0} => s.val < t.val⟩ : Frame _) ∧
    Serial (⟨fun t s : Nat => s ≤ t⟩ : Frame Nat))
end TruthCore.Modal.PastSeriality
