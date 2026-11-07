import TruthCore.Causality.PerfectionPreexistence

namespace TruthCore.Results.Causality.PerfectionPreexistence
open TruthCore.Case.Catholicism (CauseOfBeingCausesEveryPerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MoreSuchHasThePerfectionReading PerfectionsOfEffectPreexistInCauseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- A cause of a thing's being, distinct from it, causes each of its perfections
and so is more such and has them; a self-cause has them trivially. Conditional on
four OPEN premises. -/
theorem preexistFromCausalTransfer {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hTransfer : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse := by
  sorry

theorem controls : TruthCore.Causality.PerfectionPreexistence.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.PerfectionPreexistence
