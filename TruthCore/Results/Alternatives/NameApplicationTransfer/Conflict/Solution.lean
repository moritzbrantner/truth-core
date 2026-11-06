module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.Conflict

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact semantic-scope obligation; no actual reference theory is adopted. -/
theorem properExistenceRejectsNoBeing {Being : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (hTransfer : ProperReferencePreserved N god proper)
    (hExists : GodExists proper) : NoBeingRejected N god := by
  intro hNoBeing
  obtain ⟨b, hProper⟩ := hExists
  exact hNoBeing b (hTransfer b hProper)

end TruthCore.Results.Alternatives.NameApplicationTransfer.Conflict
