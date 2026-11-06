module

public import TruthCore.Causality.EternityDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EternityDefinitions.Coverage
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.EternityDefinitionFork

/-- Frozen analyst consequence; no semantic calibration or actual-life premise adopted. -/
theorem coverage (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionFork := by
  intro f
  cases hEM (BoethianDefinition f) with
  | inl h => exact Or.inl (Or.inl h)
  | inr hb =>
    cases hEM (EndlessDefinition f) with
    | inl h => exact Or.inl (Or.inr h)
    | inr he => exact Or.inr ⟨hb, he⟩

end TruthCore.Results.Causality.EternityDefinitions.Coverage
