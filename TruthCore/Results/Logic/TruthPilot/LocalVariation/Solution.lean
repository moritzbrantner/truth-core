import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.LocalVariation
open TruthCore.Logic.TruthPilot
/-- Construct a stable logical sentence and endorsement-sensitive taste sentence. A model of this encoding, not a sourced full rival worldview. -/
theorem localVariation : LogicalTruthsCompatibleWithVariation := by
  let Holds : Interpretation := fun E s => s = Sentence.logical ∨ (s = Sentence.taste ∧ E Agent.first s)
  refine ⟨Holds, ?_, ?_⟩
  · intro E
    exact Or.inl rfl
  · refine ⟨Sentence.taste, (fun _ _ => True), (fun _ _ => False), ?_, ?_⟩
    · exact Or.inr ⟨rfl, trivial⟩
    · intro h
      cases h with
      | inl h => cases h
      | inr h => exact h.2
end TruthCore.Results.Logic.TruthPilot.LocalVariation
