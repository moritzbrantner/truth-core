import TruthCore.Modal.RigidDesignation
namespace TruthCore.Results.Modal.RigidDesignation
open TruthCore.Modal.RigidDesignation
open TruthCore.Modal.PossibilityTransfer (IncludedAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box)

theorem laws : Laws := by
  intro W B m E a b w x _ _ ha hb
  have successorIff : ∀ v, m.frame.access w v →
      (CoRef a b v ↔ m.ExistsAt v x) := by
    intro v hv
    constructor
    · rintro ⟨y, hy, _⟩
      exact ((ha v hv y).mp hy).2
    · intro hx
      exact ⟨x, (ha v hv x).mpr ⟨rfl, hx⟩,
        (hb v hv x).mpr ⟨rfl, hx⟩⟩
  have iffBox : Box m.frame (CoRef a b) w ↔
      TruthCore.German.Kant.CosmologicalInference.NecessaryAt m w x :=
    ⟨fun h v hv => (successorIff v hv).mp (h v hv),
      fun h v hv => (successorIff v hv).mpr (h v hv)⟩
  refine ⟨iffBox, fun v hv hx => (successorIff v hv).mpr hx, ?_⟩
  intro inclusion necessary
  exact (TruthCore.Results.Modal.PossibilityTransfer.box_transfer_iff
    W E m.frame w).mpr inclusion (CoRef a b) (iffBox.mpr necessary)

theorem checks : Checks := by
  refine ⟨laws, ?_⟩
  unfold Controls CoRef RigidAt Box IncludedAt absentName disappearing
    epistemicModel leftName rightName E
  dsimp
  decide
end TruthCore.Results.Modal.RigidDesignation
