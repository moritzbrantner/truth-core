module

public import TruthCore.Results.Metaethics.GoodnessFormEndBoundary.Solution
public import TruthCore.Results.Metaethics.GoodnessCoverageStrength.Solution

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessSemanticCoverage
open TruthCore.Logic
open TruthCore.Metaethics.GoodnessFormEnd

theorem coverageOrDifferentDefinition (hEM : ExcludedMiddle) : SemanticNamedCoverageFork := by
  intro f s
  cases hEM (SemanticNamedCoverage s) with
  | inl h => exact Or.inl h
  | inr hNot =>
    apply Or.inr
    cases hEM (AdditionalSemanticDefinition s) with
    | inl h => exact h
    | inr hNone =>
      have hCoverage : SemanticNamedCoverage s := by
        intro d hd
        cases hEM (SemanticallyNamed s d) with
        | inl h => exact h
        | inr h => exact False.elim (hNone ⟨d, hd, h⟩)
      exact False.elim (hNot hCoverage)

theorem semanticScopeControls : SemanticScopeControls := by
  constructor
  · exact TruthCore.Results.Metaethics.GoodnessCoverageStrength.identityCoverageEntailsSemantic _ _
      TruthCore.Results.Metaethics.GoodnessFormEndBoundary.namedControls.1.1
  · refine ⟨.other, trivial, ?_⟩
    rintro (hDue | hOther)
    · exact ((hDue .knife .mass).mp ⟨rfl, rfl⟩).1
    · rcases hOther with hFeature | hApproval
      · have bad := (hFeature .counterweight .mass).mpr trivial
        cases bad.1
      · have bad := (hApproval .counterweight .mass).mpr ⟨rfl, trivial, trivial⟩
        cases bad.1
end TruthCore.Results.Metaethics.GoodnessSemanticCoverage
