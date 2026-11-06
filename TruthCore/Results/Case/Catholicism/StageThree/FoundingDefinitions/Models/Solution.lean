module

public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Models

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions

/-- Frozen semantic-comparison obligation; no preferred reading is adopted. -/
theorem definitionModels  :
    DefinitionModels := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
      (fun _ _ => True), modelSig_antecedents True,
      ⟨true, (), rfl, trivial, trivial⟩, ?_, ?_, ?_⟩
    · intro _ _ _; exact Iff.rfl
    · intro _ _ _
      constructor
      · intro _; exact Or.inl trivial
      · intro _; trivial
    · intro _ _ _ _ _; trivial
  · refine ⟨modelSig False, modelAgency False (fun p => p) True True True,
      (fun _ _ => False), modelSig_antecedents False,
      ⟨true, (), rfl, trivial, trivial⟩, ?_, ?_, ?_, modelSig_bridge_fails⟩
    · intro _ _ _; exact Iff.rfl
    · intro hInclusive
      exact (hInclusive true () rfl).2 (Or.inr ⟨trivial, trivial⟩)
    · intro hEnvoy
      exact hEnvoy true () rfl trivial trivial
  · refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
      (fun _ _ => False), modelSig_antecedents True,
      ⟨true, (), rfl, trivial, trivial⟩, ?_, ?_, ?_⟩
    · intro _ _ _
      constructor
      · intro _; exact Or.inr ⟨trivial, trivial⟩
      · intro _; trivial
    · intro hImmediate
      exact (hImmediate true () rfl).1 trivial
    · intro _ _ _ _ _; trivial
  · refine ⟨modelSig True, modelAgency True (fun p => p) True False False,
      (fun _ _ => False), modelSig_antecedents True, ⟨?_, ?_⟩, ?_⟩
    · intro hImmediate
      exact (hImmediate true () rfl).1 trivial
    · intro hInclusive
      cases (hInclusive true () rfl).1 trivial with
      | inl hDirect => exact hDirect
      | inr hEvent => exact hEvent.1
    · intro _ _ _ hFounded _
      exact False.elim hFounded
  · refine ⟨modelSig False, modelAgency False (fun p => p) True True True,
      (fun _ _ => True), modelSig_antecedents False,
      ⟨true, (), rfl, trivial, trivial⟩, ⟨?_, ?_⟩, ?_⟩
    · intro hImmediate
      exact (hImmediate true () rfl).2 trivial
    · intro hInclusive
      exact (hInclusive true () rfl).2 (Or.inl trivial)
    · intro hEnvoy
      exact hEnvoy true () rfl trivial trivial

end TruthCore.Results.Case.Catholicism.StageThree.FoundingDefinitions.Models
