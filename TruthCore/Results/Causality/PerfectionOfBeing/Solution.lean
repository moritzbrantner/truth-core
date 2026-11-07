module

public import TruthCore.Causality.PerfectionOfBeing

@[expose] public section

namespace TruthCore.Results.Causality.PerfectionOfBeing
open TruthCore.Causality.PerfectionOfBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- In act in a respect, so perfect in it, so having being. Conditional on two
OPEN premises. -/
theorem actualityOnlyInsofarAsBeing {B R : Type} (PerfectIn InAct : B → R → Prop) (esse : R)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn InAct)
    (hBeing : PerfectOnlyInsofarAsBeing PerfectIn InAct esse) :
    ActualityOnlyInsofarAsBeingReading InAct esse :=
  fun x r h => hBeing x r ((hPerfect x r).mpr h)

open TruthCore.Causality.PerfectionOfBeing.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => (h () true).mpr rfl, fun _ _ h => h.elim, fun h => Bool.noConfusion (h () true rfl)⟩,
    ⟨fun _ _ => Iff.rfl, fun h => Bool.noConfusion (h () true rfl),
      fun h => Bool.noConfusion (h () true rfl)⟩,
    ⟨fun _ _ => Iff.rfl, fun _ _ _ => trivial, fun _ _ _ => trivial⟩⟩

end TruthCore.Results.Causality.PerfectionOfBeing
