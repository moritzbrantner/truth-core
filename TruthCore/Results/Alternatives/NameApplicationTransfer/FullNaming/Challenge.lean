module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.FullNaming

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact proper-profile rejection, with transfer and an actual descriptor witness. -/
theorem noReferenceRejectsFullNaming {Being Respect : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop)
    (hTransfer : ProperReferencePreserved N god proper)
    (hNoBeing : GodNamesNoBeingReading N god)
    (hWitness : FullDescriptorExists InAct MoreIn CausesIn esse ComponentOf) :
    FullNominalNamingFails InAct MoreIn CausesIn esse ComponentOf proper := by
  sorry

end TruthCore.Results.Alternatives.NameApplicationTransfer.FullNaming
