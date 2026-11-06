module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.PureActNaming

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact proper-profile rejection, with transfer and an actual descriptor witness. -/
theorem noReferenceRejectsPureActNaming {Being Respect : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (PureAct : Being → Prop)
    (hTransfer : ProperReferencePreserved N god proper)
    (hNoBeing : GodNamesNoBeingReading N god)
    (hWitness : PureActDescriptorExists MovedIn MovesIn PureAct) :
    PureActNominalNamingFails MovedIn MovesIn PureAct proper := by
  sorry

end TruthCore.Results.Alternatives.NameApplicationTransfer.PureActNaming
