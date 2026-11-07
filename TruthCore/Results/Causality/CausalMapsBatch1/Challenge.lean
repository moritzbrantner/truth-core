import TruthCore.Causality.CausalMapsBatch1

namespace TruthCore.Results.Causality.CausalMapsBatch1
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Logic

/-- Map 1. A distinct cause of `r` in `x` has `r`; `x` has `r` received in
itself and so limited by itself; the cause's `r` is not received in `x`, so not
limited by `x`; hence the cause is more `r` than `x`. Six OPEN premises. -/
theorem causeOfQualityMoreSuch {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (ReceivedIn LimitedBy : B → R → B → Prop)
    (MoreIn : R → B → B → Prop)
    (hHas : CauseHasWhatItGives CausesIn InAct)
    (hRecv : CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn)
    (hLim : ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy)
    (hOnly : PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy)
    (hNot : CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
    (hExceed : UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) :
    CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn := by
  sorry

/-- Map 1, scoped: q.4 a.2 preexistence plus the effect's having what is caused
in it gives the weak, cause-of-being version of "nothing gives what it does not
have". -/
theorem causeOfBeingHasWhatItGives {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (esse : R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hHad : CausedPerfectionIsHad CausesIn InAct) :
    CauseOfBeingHasWhatItGives CausesIn InAct esse := by
  sorry

/-- Map 2. The effect depends on its efficient cause, the cause does not depend
on its effect, and nonmutual dependence suffices for simple priority. -/
theorem efficientCausePrior {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing)
    (hSuff : NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) :
    EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply := by
  sorry

/-- Map 2. If priority requires nonmutual dependence, nothing is prior to itself:
it would both depend and not depend on itself. -/
theorem nothingPriorToItself {B : Type} (PriorSimply DependsForBeing : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) :
    NothingPriorToItselfReading PriorSimply := by
  sorry

/-- Map 2, a second route that bypasses priority: from dependence of the effect
and independence of the cause, nothing is its own efficient cause. -/
theorem nothingEfficientCauseOfItself {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) :
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn := by
  sorry

/-- Map 2. No mutual efficient causation: if `x` also caused `c`, `c` would
depend on `x`, which its causing `x` excludes. -/
theorem noMutualEfficientCausation {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) :
    NoMutualEfficientCausation EfficientlyCausesIn := by
  sorry

/-- Map 3. A distinct mover causes, so is more such, so is in act; a self-mover
moves by a distinct part, which is therefore in act, and the whole is in act
through it. The case split on `y = x` uses excluded middle as a premise. -/
theorem nothingMovesExceptInAct {B R : Type} (MovesIn CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (PartOf : B → B → Prop)
    (hEM : ExcludedMiddle)
    (hCause : MoverCausesWhatItMovesTo MovesIn CausesIn)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hSelf : SelfMoverMovesByADistinctPart MovesIn PartOf)
    (hWhole : WholeInActThroughItsPart PartOf InAct) :
    MovesOnlyAsInActReading MovesIn InAct := by
  sorry

/-! ## Controls: each omission model and the joint witness, checked by `decide` -/

/-- The batch controls. -/
theorem controls : TruthCore.Causality.CausalMapsBatch1.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.CausalMapsBatch1
