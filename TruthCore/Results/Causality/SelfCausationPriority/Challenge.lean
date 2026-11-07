import TruthCore.Causality.SelfCausationPriority

namespace TruthCore.Results.Causality.SelfCausationPriority
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A self-cause would be prior to itself. Conditional on two OPEN premises. -/
theorem noSelfCauseFromPriority {B R : Type} (CausesIn : B → B → R → Prop)
    (PriorSimply : B → B → Prop)
    (hPrior : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply)
    (hIrreflexive : NothingPriorToItselfReading PriorSimply) :
    NothingIsEfficientCauseOfItselfReading CausesIn := by
  sorry

theorem controls : TruthCore.Causality.SelfCausationPriority.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SelfCausationPriority
