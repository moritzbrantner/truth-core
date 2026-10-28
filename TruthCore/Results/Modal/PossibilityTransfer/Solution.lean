import TruthCore.Modal.PossibilityTransfer
namespace TruthCore.Results.Modal.PossibilityTransfer
open TruthCore.Modal.PossibilityTransfer
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)

theorem diamond_transfer_iff (D : Type) (E M : TruthCore.Modal.Frame D) (w : D) :
    (∀ P : MProp D, Dia E P w → Dia M P w) ↔ IncludedAt E M w := by
  constructor
  · intro h v hEv
    obtain ⟨u, hMu, hu⟩ := h (fun u => u = v) ⟨v, hEv, rfl⟩
    exact hu ▸ hMu
  · intro h P ⟨v, hEv, hP⟩
    exact ⟨v, h v hEv, hP⟩

theorem box_transfer_iff (D : Type) (E M : TruthCore.Modal.Frame D) (w : D) :
    (∀ P : MProp D, Box M P w → Box E P w) ↔ IncludedAt E M w := by
  constructor
  · intro h v hEv
    exact h (fun u => M.access w u) (fun _ hMu => hMu) v hEv
  · intro h P hBox v hEv
    exact hBox v (h v hEv)

theorem checks : TruthCore.Modal.PossibilityTransfer.Checks := by
  refine ⟨⟨diamond_transfer_iff, box_transfer_iff⟩, ?_⟩
  unfold OmissionControl TruthCore.Modal.Reflexive TruthCore.Modal.Symmetric
    TruthCore.Modal.Transitive IncludedAt Dia Box epistemic metaphysical description
  dsimp
  decide
end TruthCore.Results.Modal.PossibilityTransfer
