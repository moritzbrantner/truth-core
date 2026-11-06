module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.Coverage

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem coverage (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionFork.{u,v,w} := by
  intro f
  cases hEM (CurrentDefinition f) with
  | inl h => exact Or.inl (Or.inl h)
  | inr hn =>
    cases hEM (TemporalDefinition f) with
    | inl h => exact Or.inl (Or.inr h)
    | inr ht => exact Or.inr ⟨hn, ht⟩

end TruthCore.Results.Causality.ComposerTemporalDefinitions.Coverage
