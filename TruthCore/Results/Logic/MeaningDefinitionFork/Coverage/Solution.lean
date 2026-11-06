module

public import TruthCore.Logic.MeaningDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.Coverage
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem definitionFork (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionFork := by
  intro L F meaningful scope
  rcases hEM (V1Definition F meaningful scope) with h1 | h1
  · exact Or.inl (Or.inl h1)
  rcases hEM (V2Definition F meaningful scope) with h2 | h2
  · exact Or.inl (Or.inr (Or.inl h2))
  rcases hEM (V3Definition F meaningful scope) with h3 | h3
  · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
  rcases hEM (AllInScopeMeaningful meaningful scope) with ha | ha
  · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))
  · exact Or.inr ⟨h1, h2, h3, ha⟩

end TruthCore.Results.Logic.MeaningDefinitionFork.Coverage
