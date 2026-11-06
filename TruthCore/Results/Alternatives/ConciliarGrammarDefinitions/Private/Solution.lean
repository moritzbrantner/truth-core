module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Private

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem neverOwnRejectsBridge (P : Practice) (hNever : DefinitionsNeverOwn P)
    (hWitness : DefinedMoveExists P) : DefinitionBridgeRejected P := by
  intro hBridge
  obtain ⟨m, hDefined⟩ := hWitness
  exact hNever m hDefined (hBridge m hDefined)

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Private
