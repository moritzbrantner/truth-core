import TruthCore.Causality.ActPriorityAtFirst
import TruthCore.Causality.ComponentFirstness
import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

namespace TruthCore.Results.Causality.ActPriorityAtFirst
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionCausingInAnotherIsEfficient)

/-- Strength order: act's simple priority over every potency of the
independently supplied potency parameter (`IndependentPriority`, the transparent
wrapper of `ActSimplyPriorToPotencyReading`) gives it at first beings. An
instance, not a new derivation. -/
theorem weakOfStrong {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop)
    (hStrong : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      InAct InPotency PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  sorry

/-- `noComponentFirst` with act priority only at first beings: a component in
potency, if first, would by the weak version have a prior being in act in that
respect, which firstness makes the component itself, against non-overlap; a
participated component has a distinct cause of its being, which is prior to it.
Conditional on five OPEN premises. As in `noComponentFirst`, one `CausesIn`
feeds both the participation premise and efficient-cause priority; the records
of that passage are a recorded defect (see the modal-spine note). -/
theorem noComponentFirstOfWeak {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherCause Participated CausesIn esse)
    (hEfficient : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  sorry

/-- The q.3 a.1 conclusion from composition, without act priority or
non-overlap: a first being is in act in some respect, so if it were in potency
in another it would be composite, so it would have a distinct cause of its
being, which by the bridge causes it efficiently and so is prior to it, against
firstness. Conditional on five OPEN premises. -/
theorem firstBeingNoPotencyOfComposition {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  sorry

/-- The weak version from composition, by `firstBeingNoPotencyOfComposition`:
a first being is in potency in no respect, so the weak version holds
vacuously. Conditional on the same five OPEN premises. -/
theorem weakOfComposition {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  sorry

open TruthCore.Causality.ActPriorityAtFirst.Control

/-- All controls and facts of the batch. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.ActPriorityAtFirst
