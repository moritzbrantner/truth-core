import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

namespace TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer

open TruthCore.Case.Catholicism.PreexistenceWithoutTransfer
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (CauseOfBeingInActAsToBeing)
open TruthCore.Case.Catholicism
  (CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll
    MaximumInBeingIsFirstBeing GodNamesTheFullyDescribedPrinciple GodExists GodIsMaximalInBeing)
open TruthCore.Causality.CausalMapsBatch1
  (CauseOfBeingHasWhatItGives CausedPerfectionIsReceivedInEffect
    ReceivedPerfectionIsLimitedByRecipient PerfectionLimitedOnlyThroughReception
    CauseHasPerfectionNotAsReceivedInEffect UnlimitedPossessionExceedsLimited)
open TruthCore.Causality.GodMaximalCausal
  (GodCausesBeingOfAllOthers MoreInIsAsymmetric SomethingOtherThanGodExists)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MoreSuchHasThePerfectionReading PerfectionsOfEffectPreexistInCauseReading
    MaximeEnsCausesBeingOfAllReading ActualityOnlyInsofarAsBeingReading
    NoComponentIsFirstBeingReading IsMaximumIn)
open TruthCore.Logic (ExcludedMiddle)

/-- A distinct cause of a thing's being is more in being than it: the cause has
being; the effect's being is received in it and so limited by it; the cause's
being is not received in the effect, so not limited by it; unlimited possession
exceeds limited. -/
theorem causeOfBeingMoreInBeing {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (ReceivedIn LimitedBy : B → R → B → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hHas : CauseOfBeingInActAsToBeing InAct CausesIn esse)
    (hRecv : CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn)
    (hLim : ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy)
    (hOnly : PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy)
    (hNot : CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
    (hExceed : UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) :
    CauseOfBeingIsMoreInBeing CausesIn MoreIn esse := by
  sorry

/-- God is maximal in being, with "more such" used only at esse: God causes
another's being, so is more in being than it and so has being; anything more in
being than God would be distinct from it and so exceeded by God, against
asymmetry. -/
theorem godMaximalFromCausingBeing {B R : Type} (IsGod : B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hCauses : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hMore : CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hAsym : MoreInIsAsymmetric MoreIn)
    (hOther : SomethingOtherThanGodExists IsGod) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  sorry

/-- Stage one from the quarta via's conclusion, with "more such" used only at
esse: the maximal cause of all being is the only maximum (another maximum has
being, so the witness causes its being and is more in being than it), causes
every perfection of every other being, and is remote from all; so the fuller
naming premise applies. -/
theorem godExistsFromMaximeEnsCausingAllByBeing {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : Being → Being → Prop) (IsGod : Being → Prop)
    (hMaxime : MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfBeingIsMoreInBeing CausesIn MoreIn esse)
    (hEM : ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

/-- Q.4 a.2 preexistence from transfer and the cause-of-being restriction: a
cause of `x`'s being causes each perfection `x` has, and a cause of a thing's
being has every perfection it causes in it. -/
theorem preexistOfTransferAndRestriction {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hTransfer : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hGives : CauseOfBeingHasWhatItGives CausesIn InAct esse) :
    PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse := by
  sorry

/-- "More such" carries distinct-cause transfer: a distinct cause of `r` in `x`
is more `r` than `x`, and what is more `r` has `r`. -/
theorem distinctCauseGivesOfMoreSuch {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    DistinctCauseHasWhatItGives CausesIn InAct := by
  sorry

/-- "More such" from distinct-cause transfer and the reception bundle; the
self-causation case of the unrestricted principle is not used. -/
theorem moreSuchOfDistinctCauseGives {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (ReceivedIn LimitedBy : B → R → B → Prop)
    (MoreIn : R → B → B → Prop)
    (hHas : DistinctCauseHasWhatItGives CausesIn InAct)
    (hRecv : CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn)
    (hLim : ReceivedPerfectionIsLimitedByRecipient ReceivedIn LimitedBy)
    (hOnly : PerfectionLimitedOnlyThroughReception ReceivedIn LimitedBy)
    (hNot : CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn)
    (hExceed : UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn) :
    CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn := by
  sorry

/-- Strength order: "more such" entails its esse instance. -/
theorem moreInBeingOfMoreSuch {B R : Type} (CausesIn : B → B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (h : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    CauseOfBeingIsMoreInBeing CausesIn MoreIn esse := by
  sorry

/-- Strength order: the unrestricted principle entails distinct-cause transfer. -/
theorem distinctCauseGivesOfCauseGives {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop)
    (h : TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) :
    DistinctCauseHasWhatItGives CausesIn InAct := by
  sorry

/-! ## Omission models and joint witnesses -/

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-- The finite controls hold. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer
