module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.Coverage

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact semantic-scope obligation; no actual reference theory is adopted. -/
theorem transferCoverage {Being : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : TransferCasesCover N god proper := by
  cases hEM (ProperReferencePreserved N god proper) with
  | inl hTransfer => exact Or.inl hTransfer
  | inr hNoTransfer =>
    cases hEM (ProperReferenceLost N god proper) with
    | inl hLost => exact Or.inr hLost
    | inr hNoLost =>
      apply False.elim
      apply hNoTransfer
      intro b hProper
      cases hEM (N.RefersTo god b) with
      | inl hRef => exact hRef
      | inr hNoRef => exact False.elim (hNoLost ⟨b, hProper, hNoRef⟩)

end TruthCore.Results.Alternatives.NameApplicationTransfer.Coverage
