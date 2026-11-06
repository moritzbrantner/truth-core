module

public import TruthCore.Alternatives.NameApplicationTransfer

@[expose] public section

namespace TruthCore.Results.Alternatives.NameApplicationTransfer.ReducedNaming

open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Exact proper-profile rejection, with transfer and an actual descriptor witness. -/
theorem noReferenceRejectsReducedNaming {Being Respect : Type} (N : NamingPractice Being) (god : N.Name)
    (proper : Being → Prop)
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTransfer : ProperReferencePreserved N god proper)
    (hNoBeing : GodNamesNoBeingReading N god)
    (hWitness : ReducedDescriptorExists InAct MoreIn CausesIn esse) :
    ReducedNominalNamingFails InAct MoreIn CausesIn esse proper := by
  intro hLeaf
  obtain ⟨m, hMax, hAll, hUnique⟩ := hWitness
  exact hNoBeing m (hTransfer m (hLeaf m hMax hAll hUnique))

end TruthCore.Results.Alternatives.NameApplicationTransfer.ReducedNaming
