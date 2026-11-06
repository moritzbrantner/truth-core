module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Exclusion

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem theologyExclusionSuppliesNeverOwn (P : Practice) (R : RoleProfile P)
    (hTheology : DefinitionsAreTheological P R)
    (hExclusion : TheologyExcludedFromOwnStandards P R) : DefinitionsNeverOwn P := by
  sorry

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Exclusion
