module
public import TruthCore.Modal.FixedInitial535
public import TruthCore.Models.FiniteSupport
@[expose] public section
namespace TruthCore.Results.Modal.FixedInitial535
open TruthCore.Modal.FixedInitial535
open TruthCore.German.Kant.CosmologicalInference
/-- Witness propagation; this elementary implication is a transcription. -/
theorem propagate {W B D : Type} (h : History W B D) (a : W)
    (hr : Rigid h a) : ∃ b, h.initial b a ∧ NecessaryAt h.ontic a b := by
  obtain ⟨⟨b, hb⟩, sound, shared⟩ := hr
  exact ⟨b, hb, fun w hw => sound b w (shared b w hw hb)⟩
theorem propagation : Propagation := fun _ _ _ h a hr => propagate h a hr
theorem controls : Controls := by
  unfold Controls RigidBranch Joint LaterVariation ConditionalOrigin Rigid SameDescription NecessaryBeing NecessaryAt profile
  dsimp
  simp [Bool.forall_bool, Bool.exists_bool, Prod.forall, Prod.exists]
theorem rigidBranch : RigidBranch := by
  unfold RigidBranch Joint LaterVariation ConditionalOrigin Rigid SameDescription NecessaryAt profile
  dsimp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    exact ⟨(false,false), ⟨rfl,rfl⟩, Or.inl rfl⟩
  · exact ⟨true, trivial, Bool.noConfusion⟩
  · intro b w hb _
    exact hb
  · intro w s t h
    exact Bool.noConfusion h.1
  · refine ⟨⟨(false,false),rfl,rfl⟩, ?_, ?_⟩
    · intro b w hb
      rcases b with ⟨tag, role⟩
      cases role
      · exact Or.inl hb.2
      · exact Bool.noConfusion hb.1
    · intro b w _ hb
      exact hb
  · intro w _
    rfl
  · intro w _
    exact Or.inl rfl
end TruthCore.Results.Modal.FixedInitial535
