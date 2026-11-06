module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Witness

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem councilSuppliesDefinedMove (P : Practice)
    (hCouncil : CouncilDefinesNaturalKnowabilityReading P) : DefinedMoveExists P := by
  obtain ⟨m, _, hDefined⟩ := hCouncil
  exact ⟨m, hDefined⟩

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Witness
