module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Description

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- The full descriptive profile supplies its theological-content component. -/
theorem descriptionSuppliesTheology (P : Practice) (R : RoleProfile P)
    (hDescription : DescriptiveTheologyGrammar P R) : DefinitionsAreTheological P R := by
  exact hDescription.1

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Description
