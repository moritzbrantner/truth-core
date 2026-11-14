module

public import TruthCore.Modal.InitialHistoryTransfer1588
public import TruthCore.Results.Modal.PossibilityTransfer.Solution
public import TruthCore.Results.Modal.FixedInitial535.Solution

@[expose] public section

namespace TruthCore.Results.Modal.InitialHistoryTransfer1588
open TruthCore.Modal.InitialHistoryTransfer1588
open TruthCore.Modal.PossibilityTransfer
open TruthCore.Modal.FixedInitial535
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)

theorem restrictedTransfer : RestrictedTransfer := by
  intro D E M P w hIn ⟨v, hEv, hP⟩
  exact ⟨v, hIn v hEv hP, hP⟩

theorem completeDescriptionTransfer : CompleteDescriptionTransfer := by
  intro D E M w v
  constructor
  · intro h hEv
    obtain ⟨u, hMu, rfl⟩ := h ⟨v, hEv, rfl⟩
    exact hMu
  · intro h ⟨u, hEu, hu⟩
    subst hu
    exact ⟨u, h hEu, rfl⟩

theorem transferRefinement : TransferRefinement :=
  ⟨restrictedTransfer, completeDescriptionTransfer⟩

/-- Composes the #535 propagation theorem: an M-accessible bearer-omitting
history would have to contain the actual initial bearer. -/
theorem rigidTriad : RigidTriad := by
  intro W B D h E a b hr hb ⟨v, hEv, hAbsent⟩ hIn
  have hMv := hIn v hEv hAbsent
  exact hAbsent (hr.2.1 b v (hr.2.2 b v hMv hb))

/-- Composes #535 propagation with the #438 box-transfer law. -/
theorem rigidInclusionNecessity : RigidInclusionNecessity := by
  intro W B D h E a hr hIn
  obtain ⟨b, hb, hNec⟩ := TruthCore.Results.Modal.FixedInitial535.propagate h a hr
  exact ⟨b, hb, (TruthCore.Results.Modal.PossibilityTransfer.box_transfer_iff W E
    h.ontic.frame a).2 hIn _ hNec⟩

theorem model : Model := by
  unfold Model TruthCore.Modal.Reflexive TruthCore.Modal.Symmetric
    TruthCore.Modal.Transitive Rigid LaterVariation NecessaryAt IncludedAt
    IncludedOn AltBearer AltType SameDescription sameTypeAltBearer Dia Box
    history4 epistemic4 rigidAccess descAccess root
  dsimp
  and_intros
  all_goals decide

theorem checks : TruthCore.Modal.InitialHistoryTransfer1588.Checks :=
  ⟨transferRefinement, rigidTriad, rigidInclusionNecessity, model⟩
end TruthCore.Results.Modal.InitialHistoryTransfer1588
