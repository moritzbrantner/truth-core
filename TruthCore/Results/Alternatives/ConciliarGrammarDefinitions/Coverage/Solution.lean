module

public import TruthCore.Alternatives.ConciliarGrammarDefinitions

@[expose] public section

namespace TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Coverage

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.ConciliarGrammarDefinitions

/-- Exact normative-role consequence; a descriptive theology label alone is insufficient. -/
theorem definitionStatusCoverage (P : Practice) (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionStatusCases P := by
  cases hEM (DefinitionIsOwnStandardReading P) with
  | inl h => exact Or.inl h
  | inr hNotOwn =>
    cases hEM (DefinitionsNeverOwn P) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hNotNever =>
      apply Or.inr; apply Or.inr
      constructor
      · cases hEM (∃ m, P.Defined m ∧ P.OwnStandard m) with
        | inl h => exact h
        | inr hNone =>
          exact False.elim (hNotNever (fun m hDefined hOwn => hNone ⟨m, hDefined, hOwn⟩))
      · cases hEM (∃ m, P.Defined m ∧ ¬ P.OwnStandard m) with
        | inl h => exact h
        | inr hNone =>
          apply False.elim; apply hNotOwn
          intro m hDefined
          cases hEM (P.OwnStandard m) with
          | inl h => exact h
          | inr h => exact False.elim (hNone ⟨m, hDefined, h⟩)

end TruthCore.Results.Alternatives.ConciliarGrammarDefinitions.Coverage
