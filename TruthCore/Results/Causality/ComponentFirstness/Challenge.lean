import TruthCore.Causality.ComponentFirstness

namespace TruthCore.Results.Causality.ComponentFirstness
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A component is in potency or participated. If in potency, act priority gives
something in act prior to it, firstness makes that thing the component itself,
and it would be in act and in potency in one respect. If participated, it has a
distinct cause of its being, which is prior to it, against firstness.
Conditional on five OPEN premises. -/
theorem noComponentFirst {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherCause Participated CausesIn esse)
    (hEfficient : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  sorry

theorem controls : TruthCore.Causality.ComponentFirstness.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ComponentFirstness
