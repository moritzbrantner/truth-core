module

public import TruthCore.Logic.CollectivePossibilityRouteBoundary

@[expose] public section
namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Controls
open TruthCore.Logic
open TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Frozen scope obligation; no historical interpretation or premise truth asserted. -/
theorem controls : Controls := by
  have hEach : ∀ x : Bool, ∃ t : Bool, ¬ x = t := by
    intro x
    cases x with
    | false => exact ⟨true, Bool.noConfusion⟩
    | true => exact ⟨false, Bool.noConfusion⟩
  have noAlternatingEmpty : JointAbsenceImpossible alternating := by
    intro h
    obtain ⟨t, ht⟩ := h
    exact ht t rfl
  have noDisallowedEmpty : JointAbsenceImpossible disallowedCommon := by
    intro h
    obtain ⟨b, hb⟩ := h
    exact hb b rfl
  refine ⟨TruthCore.Results.Logic.QuantifierShiftInvalid.quantifierShiftInvalid,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, noAlternatingEmpty⟩,
    ?_, ?_, ?_, ?_, noDisallowedEmpty⟩
  · intro _; exact ⟨false, fun _ => Bool.noConfusion⟩
  · intro x hx; exact hx
  · intro φ h; exact h
  · intro x; exact ⟨false, Bool.noConfusion⟩
  · intro _; exact ⟨false, fun _ => Bool.noConfusion⟩
  · intro h
    obtain ⟨t, ht⟩ := h hEach
    exact ht t rfl
  · intro x hx; exact hx
  · intro φ h; exact h
  · intro x; exact hEach x
  · intro _; exact ⟨none, fun _ h => by cases h⟩
  · intro x hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨some b, hb⟩
  · intro h
    exact noDisallowedEmpty (h ⟨none, fun _ h => by cases h⟩)
  · intro x
    cases x with
    | false => exact ⟨true, fun h => Bool.noConfusion (Option.some.inj h)⟩
    | true => exact ⟨false, fun h => Bool.noConfusion (Option.some.inj h)⟩

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Controls
