import TruthCore.Causality.ActPriorityThetaEight
import TruthCore.Results.Causality.ActPriorityAtFirst.Solution

namespace TruthCore.Results.Causality.ActPriorityThetaEight
open TruthCore.Causality.ActPriorityThetaEight
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionCausingInAnotherIsEfficient)

/-- Θ.8, the eternal: a first being is in act in some respect, namely in being,
because it cannot fail to be (OPEN) and whatever is simply incorruptible is in
act in substance (*In Metaph.* IX lect. 9 n. 5-6 reading). -/
theorem inActOfIncorruptible {B R : Type} (InAct CanFailToBe : B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse) :
    FirstBeingIsInSomeAct InAct PriorSimply := by
  sorry

/-- Strength order: the composition premise gives its instance at act in
being. -/
theorem restrictedOfComposition {B R : Type} (InAct InPotency : B → R → Prop) (esse : R)
    (Composite : B → Prop)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite) :
    ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite := by
  sorry

/-- Θ.8, the eternal, with composition: a first being cannot fail to be, so it
is in act in being; if it were in potency in some respect it would be
composite, so it would have a distinct cause of its being, which by the bridge
causes it efficiently and so is prior to it, against firstness. Composes
`firstBeingNoPotencyOfComposition` at act read as act in being. Conditional on
six OPEN premises. -/
theorem firstBeingNoPotencyOfThetaEight {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  sorry

/-- Plenitude plus change-cause: a first being in potency in a respect now can
be in act in it (definitional priority read as an open bridge); by plenitude
over an infinite past it was in act in it at some earlier time; so it has an
efficient cause other than itself, which is prior to it, against firstness.
Concludes no potency at `now` only. Uses no composition premise and no cause of
composites. Conditional on five OPEN premises. -/
theorem firstBeingNoPotencyOfPlenitude {B R T : Type}
    (InActAt InPotencyAt : T → B → R → Prop) (PriorSimply : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (Before : T → T → Prop) (now : T)
    (Possible : (T → Prop) → Prop)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hPast : PastIsInfinite Before now)
    (hPossible : PotencyMakesActPossible InActAt InPotencyAt Possible)
    (hChange : ActThenPotencyHasAnotherCause Before InActAt InPotencyAt EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingIsInNoWayInPotencyAt InPotencyAt PriorSimply now := by
  sorry

/-- The weak version from the Θ.8 route: by `firstBeingNoPotencyOfThetaEight`
a first being is in potency in no respect, so first-being act priority holds
vacuously. Same six OPEN premises, all with the independent POTENCY_2
parameter. -/
theorem weakOfThetaEight {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  sorry

open TruthCore.Causality.ActPriorityThetaEight.Control

/-- All controls and facts of the batch. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.ActPriorityThetaEight
