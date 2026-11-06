module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Mixed

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem mixedRejectsUniform (P : Practice) (hMixed : MixedDefinitionStatus P) : UniformDefinitionStatusRejected P := by
  obtain ⟨⟨m, hDefinedM, hOwnM⟩, n, hDefinedN, hNotOwnN⟩ := hMixed
  constructor
  · intro hBridge; exact hNotOwnN (hBridge n hDefinedN)
  · intro hNever; exact hNever m hDefinedM hOwnM

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Mixed
