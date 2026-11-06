module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.Strength

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact semantic-scope obligation; no actual reference theory is adopted. -/
theorem coextensionPreserves {Being : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (hShared : SharedReferenceExtension N god proper) :
    ProperReferencePreserved N god proper := by
  sorry

end TruthCore.Results.Alternatives.NameApplicationTransfer.Strength
