import TruthCore.Comparison.RoweEvil
import TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.Solution

namespace TruthCore.Results.Comparison.ProblemOfEvil.RoweApparentCompatibility
open TruthCore.English.Rowe TruthCore.Comparison.RoweEvil

/-- Finite interpretation with an actual, unrecognized greater-good cost.
All predicates have explicit case-sensitive extensions. No claim is made
that these extensions describe actual suffering, God, or epistemic warrant. -/
def model : Sig where
  Being := Bool
  Event := Bool
  Outcome := Bool
  Omniscient b := b = true
  Omnipotent b := b = true
  WhollyGood b := b = true
  Occurs e := e = false
  IntenseSuffering e := e = false
  CanPrevent b e := b = true ∧ e = false
  Cost b e o := b = true ∧ e = false ∧ o = true
  GreaterGood o e := o = true ∧ e = false
  EqualOrWorseEvil o e := o = false ∧ e = true
  RecognizesCost b e o := b = false ∧ e = true ∧ o = false

theorem roweApparentCompatibility : ApparentCompatibility := by
  have hPermission : PermissionConstraintReading model := by
    intro b e hKnows _ hOccurs _ _
    exact ⟨true, ⟨hKnows, hOccurs, rfl⟩, Or.inl ⟨rfl, hOccurs⟩⟩
  have hTheism : TheisticBeingExists model := ⟨true, rfl, rfl, rfl⟩
  refine ⟨model, hPermission, ?_, hTheism, ?_⟩
  · refine ⟨false, rfl, rfl, ?_⟩
    intro b hKnows _
    refine ⟨⟨hKnows, rfl⟩, ?_⟩
    rintro ⟨o, hCost, hRecognizes, _⟩
    exact Bool.noConfusion (hCost.1.symm.trans hRecognizes.1)
  · intro hGratuitous
    exact RoweDeductiveCore.roweDeductiveCore model hGratuitous hPermission hTheism

end TruthCore.Results.Comparison.ProblemOfEvil.RoweApparentCompatibility
