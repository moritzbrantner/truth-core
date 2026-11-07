import TruthCore.Causality.GodMaximalCausal

namespace TruthCore.Results.Causality.GodMaximalCausal
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Case.Catholicism (GodIsMaximalInBeing)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae (MoreSuchHasThePerfectionReading)
open TruthCore.Logic (ExcludedMiddle)

/-- God causes another's being, so is more in being than it and so has being;
anything more in being than God would be distinct from it and so exceeded by God,
against asymmetry. Conditional on six OPEN premises. -/
theorem godMaximalFromCausing {B R : Type} (IsGod : B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hCauses : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hAsym : MoreInIsAsymmetric MoreIn)
    (hOther : SomethingOtherThanGodExists IsGod) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  sorry

theorem controls : TruthCore.Causality.GodMaximalCausal.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.GodMaximalCausal
