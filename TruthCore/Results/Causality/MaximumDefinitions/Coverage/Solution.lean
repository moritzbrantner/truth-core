module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.Coverage
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst interface; no real-world degree interpretation is adopted. -/
theorem coverage {Degree : Type} [Preorder Degree] (hEM : TruthCore.Logic.ExcludedMiddle) :
    DefinitionFork (Degree := Degree) := by
  intro f
  cases hEM (MaximalDefinition f) with
  | inl h => exact Or.inl (Or.inl h)
  | inr hm =>
    cases hEM (GreatestDefinition f) with
    | inl h => exact Or.inl (Or.inr (Or.inl h))
    | inr hg =>
      cases hEM (StrictDefinition f) with
      | inl h => exact Or.inl (Or.inr (Or.inr h))
      | inr hs => exact Or.inr ⟨hm, hg, hs⟩

end TruthCore.Results.Causality.MaximumDefinitions.Coverage
