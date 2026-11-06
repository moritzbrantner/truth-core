module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions
public import TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Exclusion.Solution
public import TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Private.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Scope

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem theologyExclusionRejectsBridge (P : Practice) (R : RoleProfile P)
    (hTheology : DefinitionsAreTheological P R)
    (hExclusion : TheologyExcludedFromOwnStandards P R)
    (hWitness : DefinedMoveExists P) : DefinitionBridgeRejected P := by
  exact TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Private.neverOwnRejectsBridge P
    (TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Exclusion.theologyExclusionSuppliesNeverOwn
      P R hTheology hExclusion) hWitness

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Scope
