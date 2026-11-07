module

public import TruthCore.Causality.SelfCausationPriority

@[expose] public section

namespace TruthCore.Results.Causality.SelfCausationPriority
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A self-cause would be prior to itself. Conditional on two OPEN premises. -/
theorem noSelfCauseFromPriority {B R : Type} (CausesIn : B → B → R → Prop)
    (PriorSimply : B → B → Prop)
    (hPrior : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply)
    (hIrreflexive : NothingPriorToItselfReading PriorSimply) :
    NothingIsEfficientCauseOfItselfReading CausesIn :=
  fun x r h => hIrreflexive x (hPrior x x r h)

open TruthCore.Causality.SelfCausationPriority.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => h () () () rfl, fun _ h => h, fun h => h () () rfl⟩,
    ⟨fun _ _ _ _ => trivial, fun h => h () trivial, fun h => h () () rfl⟩,
    ⟨fun _ _ _ h => h.elim, fun _ h => h, fun _ _ h => h⟩⟩

end TruthCore.Results.Causality.SelfCausationPriority
