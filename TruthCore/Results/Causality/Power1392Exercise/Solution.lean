module
public import TruthCore.Causality.Power1392Exercise
@[expose] public section
namespace TruthCore.Results.Causality.Power1392Exercise
open TruthCore.Causality.Power1392Exercise
theorem actualIntrinsic : Actual.falseAssertion = false ∧
    (∃ e, Intrinsic true e ∧ Success (.assertFalse true) e) := by
  exact ⟨rfl, ⟨⟨true, true, false⟩, rfl, rfl, rfl⟩⟩
theorem separatingControl : Generic (.assertFalse true) ∧
    ¬ Joint true (.assertFalse true) ∧ Joint true (.revealTrue true) := by
  refine ⟨⟨⟨true, true, false⟩, rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨e, ha, hs⟩
    have ht := ha.2 rfl
    have hf := hs.2
    rw [ht] at hf
    cases hf
  · exact ⟨⟨true, false, true⟩, ⟨rfl, fun _ => rfl⟩, rfl, rfl, rfl⟩

theorem certificate : Certificate := ⟨actualIntrinsic, separatingControl⟩
end TruthCore.Results.Causality.Power1392Exercise
