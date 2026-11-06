module

public import TruthCore.Alternatives.NameApplicationTransfer
public import TruthCore.Results.Alternatives.FideismReference.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.Description

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact semantic-scope obligation; no actual reference theory is adopted. -/
theorem properDescriptionExcluded {Being Respect : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop)
    (hTransfer : ProperReferencePreserved N god proper)
    (hLeaf : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf proper)
    (hNoBeing : GodNamesNoBeingReading N god) :
    FullDescriptionExcluded InAct MoreIn CausesIn esse ComponentOf := by
  sorry

end TruthCore.Results.Alternatives.NameApplicationTransfer.Description
