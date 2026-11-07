import TruthCore.Causality.TermSenseForks

/-! Sense forks for "prior" and "cause": joint theorems by cases over the sense
enums, per-branch results, uses-agree from exclusivity, and controls.
Analyst formulations, attribution deferred. -/

namespace TruthCore.Results.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TermSenseForks

/-! ## "prior" -/

/-- Joint theorem by cases over `PrioritySense`. If the route's "prior" is read
in one of the three senses (coverage) and act is prior to potency in that
sense, then act is simply prior to potency: the simple branch gives it
directly, the substance branch through the open bridge from priority in
substance to simple priority, and the temporal branch is impossible because a
temporally first being is in potency. -/
theorem actSimplyPriorBySenseFork {Being Respect : Type}
    (F : PriorityFrame Being Respect) (Select : PrioritySense → Prop)
    (RoutePrior : Being → Being → Prop)
    (hCover : PriorSensesExhaustive F Select (fun _ : Unit => RoutePrior))
    (hRoute : ActPriorInRouteSense F RoutePrior)
    (hBridge : PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply)
    (hFirst : TemporallyFirstBeingInPotency F) :
    ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply := by
  sorry

/-- The temporal branch is refuted: if some temporally first being is in
potency, act is not prior to potency in time. -/
theorem actNotPriorInTime {Being Respect : Type} (F : PriorityFrame Being Respect)
    (hFirst : TemporallyFirstBeingInPotency F) : ActNotPriorInTime F := by
  sorry

/-- The substance branch: act's priority in substance over every potency, with
the open bridge to simple priority, gives act's simple priority. -/
theorem actSimplyPriorFromSubstance {Being Respect : Type}
    (F : PriorityFrame Being Respect)
    (hSubst : ActPriorInSubstance F)
    (hBridge : PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply) :
    ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply := by
  sorry

/-- Coverage and exclusivity block equivocation: every use of "prior" on the
route stands for one relation. -/
theorem priorRouteUsesAgree {Being Respect : Type} {U : Type}
    (F : PriorityFrame Being Respect) (Select : PrioritySense → Prop)
    (use : U → Being → Being → Prop)
    (hCover : PriorSensesExhaustive F Select use)
    (hUnique : PriorSenseUnique Select) :
    PriorRouteUsesAgree use := by
  sorry

/-! ## "cause" -/

/-- Joint theorem by cases over `CauseSense`. If the route's "cause" in
"nothing causes itself" is read in one of the four senses (coverage), then
nothing is its own efficient cause: the efficient branch gives it directly, the
moving branch (Aristotle's reading that no mover moves itself) through the open
bridge that self-efficient causation would be self-moving, the origin branch
through the open bridge that it would be self-origination, and the perfection
branch is impossible because some subject causes its own perfection. -/
theorem noSelfEfficientCauseBySenseFork {Being Respect : Type}
    (F : CauseFrame Being Respect) (Select : CauseSense → Prop)
    (RouteCause : Being → Being → Respect → Prop)
    (hCover : CauseSensesExhaustive F Select (fun _ : Unit => RouteCause))
    (hRoute : NothingCausesItselfInRouteSense RouteCause)
    (hPerf : SomeSubjectCausesItsOwnPerfection F)
    (hMove : SelfEfficientCausationIsSelfMoving F)
    (hOrigin : SelfEfficientCausationIsSelfOrigination F) :
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn := by
  sorry

/-- The perfection branch is refuted: a self-perfecting subject falsifies
"nothing causes a perfection in itself". -/
theorem ownPerfectionNotAlwaysExternal {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hPerf : SomeSubjectCausesItsOwnPerfection F) :
    OwnPerfectionNotAlwaysExternal F := by
  sorry

/-- The moving branch: Aristotle's reading that no mover moves itself, with
the open bridge, gives that nothing is its own efficient cause. -/
theorem noSelfEfficientCauseFromNoSelfMover {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hNoSelf : TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
      F.MovesIn)
    (hMove : SelfEfficientCausationIsSelfMoving F) :
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn := by
  sorry

/-- The origin branch: no self-origination, with the open bridge, gives that
nothing is its own efficient cause. -/
theorem noSelfEfficientCauseFromOrigin {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hNoOrigin : NothingOriginatesItself F)
    (hOrigin : SelfEfficientCausationIsSelfOrigination F) :
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn := by
  sorry

/-- Strength order: Aristotle's unrestricted reading (no mover moves itself in
any respect) implies the prima via's same-respect reading. -/
theorem noSelfMovingSameRespectFromNoSelfMover {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hAny : TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
      MovesIn) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn := by
  sorry

/-- Coverage and exclusivity block equivocation on "cause". -/
theorem causeRouteUsesAgree {Being Respect : Type} {U : Type}
    (F : CauseFrame Being Respect) (Select : CauseSense → Prop)
    (use : U → Being → Being → Respect → Prop)
    (hCover : CauseSensesExhaustive F Select use)
    (hUnique : CauseSenseUnique Select) :
    CauseRouteUsesAgree use := by
  sorry

/-! ## Controls -/

/-- The batch controls. -/
theorem controls : TermSenseForkControls := by
  sorry

end TruthCore.Results.Causality.TermSenseForks
