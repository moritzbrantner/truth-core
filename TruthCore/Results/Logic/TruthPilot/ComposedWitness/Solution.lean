import TruthCore.Logic.TruthComposition
import TruthCore.Results.Logic.TruthPilot.ConsequencePair.Solution
import TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.Solution
import TruthCore.Results.Logic.TruthPilot.SomeImpliesNotAll.Solution

namespace TruthCore.Results.Logic.TruthPilot.ComposedWitness
open TruthCore.Logic.TruthComposition

/-- Compose an independently grounded witness through the pilot intermediate.
This is a logical conjunction, not a claim of empirical or source verification. -/
theorem composedWitness : WitnessAndConsequence := by
  have hWitness := TruthCore.Results.Logic.TruthPilot.SomePropositionHolds.somePropositionHolds
  have hIntermediate := TruthCore.Results.Logic.TruthPilot.SomeImpliesNotAll.someImpliesNotAll hWitness
  exact TruthCore.Results.Logic.TruthPilot.ConsequencePair.pairFromConsequence hIntermediate

end TruthCore.Results.Logic.TruthPilot.ComposedWitness
