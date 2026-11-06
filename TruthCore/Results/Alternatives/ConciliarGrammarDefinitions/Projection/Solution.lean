module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Projection

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem uniformRejectionIncludesBridge (P : Practice) (hBoth : UniformDefinitionStatusRejected P) : DefinitionBridgeRejected P := by
  exact hBoth.1

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Projection
