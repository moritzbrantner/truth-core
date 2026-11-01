import TruthCore.Modal.LimitationPossibility
namespace TruthCore.Results.Modal.LimitationPossibility
open TruthCore.Modal.LimitationPossibility
open TruthCore.Isabelle.AFP.GoedelGod
open TruthCore.Logic (ExcludedMiddle)
/-- Four explicit inputs; no frame law, full deficiency semantics, Scott A1a,
actual NB or source-premise truth is assumed or concluded. -/
theorem possible {W B : Type} (F : TruthCore.Modal.Frame W)
    (L : Property W B → W → Prop) (Q Phi : Property W B) (w : W)
    (hKnown : KnownLimitingAt L Q w) (hTarget : NonlimitingAt L Phi w)
    (hClosure : BackwardClosedAt F L w) (hEM : ExcludedMiddle) :
    PossiblyExemplifiedAt F Phi w := by
  rcases hEM (PossiblyExemplifiedAt F Phi w) with hPossible | hImpossible
  · exact hPossible
  · have hInclusion : Box F (fun v => ∀ x, Phi x v → Q x v) w := by
      intro v hwv x hx
      exact (hImpossible ⟨v, hwv, x, hx⟩).elim
    exact (hTarget (hClosure Phi Q hInclusion hKnown)).elim
end TruthCore.Results.Modal.LimitationPossibility
