import TruthCore.Ethics.HardMoralCases
namespace TruthCore.Results.Ethics.HardMoralCases
open TruthCore.Ethics.HardMoralCases TruthCore.Ethics.MoralAccessFibers
open TruthCore.Modal.DeonticFutureBoundary
/-- Finite omission and feasible conflict controls. -/
theorem certificate : TruthCore.Ethics.HardMoralCases.Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨⟨true, true, true⟩, true, true⟩, ⟨⟨true, true, true⟩, true, false⟩, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro h; cases h
  · refine ⟨⟨true, true, true⟩, ⟨true, true, false⟩, rfl, rfl, rfl, ?_⟩
    intro h; cases h
  · refine ⟨⟨fun _ v => v = true⟩, ⟨fun _ v => v = false⟩, ⟨fun _ _ => True⟩, (fun _ => True), trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨true, rfl, trivial⟩
    · exact ⟨false, rfl, trivial⟩
    · exact ⟨true, trivial, rfl⟩
    · exact ⟨false, trivial, rfl⟩
    · intro v h; exact h
    · intro v h; exact h
end TruthCore.Results.Ethics.HardMoralCases
