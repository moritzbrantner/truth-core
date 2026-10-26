import TruthCore.Explanation.ExistencePSR

namespace TruthCore.Results.Explanation.PSRScope
open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference

theorem psrScopeBoundary : PsrScopeBoundary := by
  constructor
  · let m : Model Bool Bool := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun _ x => x = false
        Causes := fun _ _ _ => False }
      explains := fun _ r f => match f with
        | .fact x => r = .intrinsic x ∧ x = false }
    refine ⟨m, (fun _ _ => True.intro), ?_, ?_, ?_, ?_⟩
    · intro w x r h
      exact h.2
    · intro w x hx
      exact ⟨.intrinsic x, rfl, hx⟩
    · refine ⟨false, rfl, ?_⟩
      intro _ _
      rfl
    · intro h
      obtain ⟨_, _, _, hc⟩ := h false false rfl
      exact hc.elim
  · let m : Model Bool Bool := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun w x => x = false ∨ (w = false ∧ x = true)
        Causes := fun _ _ _ => False }
      explains := fun w r f => match f with
        | .fact x => w = false ∧ x = true ∧ r = .circumstance x }
    refine ⟨m, (fun _ _ => True.intro), ?_, ?_, ?_, ?_, ?_⟩
    · intro w x r h
      exact Or.inr ⟨h.1, h.2.1⟩
    · intro w x hc
      cases w with
      | false =>
        cases x with
        | false =>
          obtain ⟨_, v, _, hv⟩ := hc
          exact (hv (Or.inl rfl)).elim
        | true =>
          exact ⟨.circumstance true, rfl, rfl, rfl⟩
      | true =>
        cases x with
        | false =>
          obtain ⟨_, v, _, hv⟩ := hc
          exact (hv (Or.inl rfl)).elim
        | true =>
          rcases hc.1 with h | ⟨h, _⟩
          · exact Bool.noConfusion h
          · exact Bool.noConfusion h
    · refine ⟨Or.inr ⟨rfl, rfl⟩, true, True.intro, ?_⟩
      rintro (h | ⟨h, _⟩)
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · refine ⟨false, Or.inl rfl, ?_⟩
      intro _ _
      exact Or.inl rfl
    · intro hp
      obtain ⟨_, h⟩ := hp false false (Or.inl rfl)
      exact Bool.noConfusion h.2.1

end TruthCore.Results.Explanation.PSRScope
