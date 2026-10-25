import TruthCore.Modal.S5Research
import TruthCore.Results.Modern.Hume.Conceivability.Solution
namespace TruthCore.Results.Modal.S5.SymmetryBoundary
open TruthCore.Modal TruthCore.Modal.ResearchFixture TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (Dia)
open TruthCore.Modern.Hume.Conceivability (branching Collapse Contingent)
theorem checks : SymmetryBoundary := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hb, _, _⟩ :=
    TruthCore.Results.Modern.Hume.Conceivability.checks
  refine ⟨hb.1, hb.2.1, ?_, ?_, ?_, ?_⟩
  · intro h
    have bad := h false true (Or.inl rfl)
    cases bad with
    | inl ht => exact Bool.noConfusion ht
    | inr hf => exact Bool.noConfusion hf
  · obtain ⟨v, hv, hc⟩ := hb.2.2.1
    exact ⟨v, hv, (full_iff_hume branching v).mpr hc⟩
  · intro h
    exact hb.2.2.2 ((full_iff_hume branching false).mp h)
  · exact ⟨⟨true, Or.inl rfl, rfl⟩, ⟨false, Or.inl rfl, Bool.noConfusion⟩⟩
end TruthCore.Results.Modal.S5.SymmetryBoundary
