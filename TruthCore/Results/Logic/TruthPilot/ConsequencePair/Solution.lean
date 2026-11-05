module

public import TruthCore.Logic.TruthComposition
public import TruthCore.Results.Logic.TruthPilot.NotAllImpliesSome.Solution

@[expose] public section

namespace TruthCore.Results.Logic.TruthPilot.ConsequencePair
open TruthCore.Logic.TruthPilot TruthCore.Logic.TruthComposition

/-- The final B → C bridge of the bounded composition fixture. -/
theorem pairFromConsequence (hIntermediate : NotEveryPropositionFails) : WitnessAndConsequence := by
  have hWitness := TruthCore.Results.Logic.TruthPilot.NotAllImpliesSome.notAllImpliesSome hIntermediate
  exact ⟨hWitness, hIntermediate⟩

end TruthCore.Results.Logic.TruthPilot.ConsequencePair
