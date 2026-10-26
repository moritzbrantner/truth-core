import TruthCore.Models.FiniteSupport
import TruthCore.Explanation.ExistencePSR

/-! Named finite interpretations and closed certificates for #414.
Registration tests formal consequence only; it does not establish metaphysical possibility.
Existing Challenges and proof obligations are unchanged. -/
namespace TruthCore.Models.PSR
open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference
namespace Intrinsic
def model : Model Bool Bool := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun _ x => x = false
        Causes := fun _ _ _ => False }
      explains := fun _ r f => match f with
        | .fact x => r = .intrinsic x ∧ x = false }
theorem evaluation0 : @TruthCore.Explanation.ExistencePSR.Sound (Bool) (Bool) (TruthCore.Models.PSR.Intrinsic.model) := by
  intro w x r h
  exact h.2

theorem evaluation1 : @TruthCore.Explanation.ExistencePSR.ExistencePSR (Bool) (Bool) (TruthCore.Models.PSR.Intrinsic.model) := by
  intro w x hx
  exact ⟨.intrinsic x, rfl, hx⟩

theorem evaluation2 : @TruthCore.German.Kant.CosmologicalInference.NecessaryBeing (Bool) (Bool) (TruthCore.Models.PSR.Intrinsic.model.ontic) (false) := by
  refine ⟨false, rfl, ?_⟩
  intro _ _
  rfl

theorem evaluation3 : ¬ (@TruthCore.Explanation.ExistencePSR.EveryExistentExternallyCaused (Bool) (Bool) (TruthCore.Models.PSR.Intrinsic.model)) := by
  intro h
  obtain ⟨_, _, _, hc⟩ := h false false rfl
  exact hc.elim

end Intrinsic
namespace ContingentOnly
def model : Model Bool Bool := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun w x => x = false ∨ (w = false ∧ x = true)
        Causes := fun _ _ _ => False }
      explains := fun w r f => match f with
        | .fact x => w = false ∧ x = true ∧ r = .circumstance x }
theorem evaluation0 : @TruthCore.Explanation.ExistencePSR.Sound (Bool) (Bool) (TruthCore.Models.PSR.ContingentOnly.model) := by
  intro w x r h
  exact Or.inr ⟨h.1, h.2.1⟩

theorem evaluation1 : @TruthCore.Explanation.ExistencePSR.ContingentPSR (Bool) (Bool) (TruthCore.Models.PSR.ContingentOnly.model) := by
  intro w x hc
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

theorem evaluation2 : @TruthCore.German.Kant.CosmologicalInference.ContingentAt (Bool) (Bool) (TruthCore.Models.PSR.ContingentOnly.model.ontic) (false) (true) := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, true, True.intro, ?_⟩
  rintro (h | ⟨h, _⟩)
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h

theorem evaluation3 : @TruthCore.German.Kant.CosmologicalInference.NecessaryBeing (Bool) (Bool) (TruthCore.Models.PSR.ContingentOnly.model.ontic) (false) := by
  refine ⟨false, Or.inl rfl, ?_⟩
  intro _ _
  exact Or.inl rfl

theorem evaluation4 : ¬ (@TruthCore.Explanation.ExistencePSR.ExistencePSR (Bool) (Bool) (TruthCore.Models.PSR.ContingentOnly.model)) := by
  intro hp
  obtain ⟨_, h⟩ := hp false false (Or.inl rfl)
  exact Bool.noConfusion h.2.1

end ContingentOnly
end TruthCore.Models.PSR
