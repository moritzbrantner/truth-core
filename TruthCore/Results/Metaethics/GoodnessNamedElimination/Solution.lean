module

public import TruthCore.Metaethics.GoodnessFormEnd

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessNamedElimination
open TruthCore.Logic
open TruthCore.Metaethics.GoodnessFormEnd

theorem namedCoverageFork (hEM : ExcludedMiddle) : NamedCoverageFork := by
  intro f s
  cases hEM (NamedCoverage s) with
  | inl h => exact Or.inl h
  | inr hNot =>
    apply Or.inr
    cases hEM (AdditionalRelevantDefinition s) with
    | inl h => exact h
    | inr hNone =>
      have hCoverage : NamedCoverage s := by
        intro d hd
        cases hEM (Named s d) with
        | inl h => exact h
        | inr h => exact False.elim (hNone ⟨d, hd, h⟩)
      exact False.elim (hNot hCoverage)

/-- Inadequacy only eliminates a named branch when it negates that branch's
correctness. Coverage and the correct-account witness are explicit inputs. -/
theorem dueFromNamedElimination (f : Frame) (s : DefinitionSpace f)
    (hCoverage : NamedCoverage s) (hCorrect : CorrectAccountExists s)
    (hFeature : FeatureAccountFails s) (hApproval : ApprovalAccountFails s) :
    DueActualityThesis f := by
  obtain ⟨d, hAdmissible, hDescription⟩ := hCorrect
  rcases hCoverage d hAdmissible with hDue | hOther
  · rw [hDue] at hDescription
    intro x p
    exact (hDescription x p).trans (s.dueMeaning x p)
  · rcases hOther with hNatural | hAttitude
    · rw [hNatural] at hDescription
      exact False.elim (hFeature hDescription)
    · rw [hAttitude] at hDescription
      exact False.elim (hApproval hDescription)

end TruthCore.Results.Metaethics.GoodnessNamedElimination
