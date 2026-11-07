import TruthCore.Causality.Round2PerfectionPrimacy

namespace TruthCore.Results.Causality.Round2PerfectionPrimacy

open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.ComponentFirstness
open TruthCore.Causality.ReceptionLimitation
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception
open TruthCore.Case.Catholicism

/-- Target 1. `x`'s limited degree is within its own capacity; `c`'s having `r`
not limited by `x` exceeds that capacity; so `c`'s degree is greater, and the
greater degree is more. -/
theorem unlimitedPossessionExceedsLimited {B R D : Type} [Preorder D]
    (InAct : B → R → Prop) (LimitedBy : B → R → B → Prop) (MoreIn : R → B → B → Prop)
    (deg cap : B → R → D)
    (hWithin : LimitedHavingIsWithinCapacity LimitedBy deg cap)
    (hBeyond : UnlimitedHavingExceedsCapacity InAct LimitedBy deg cap)
    (hMore : GreaterDegreeIsMore MoreIn deg) :
    UnlimitedPossessionExceedsLimited InAct LimitedBy MoreIn := by
  sorry

/-- Target 2. What `x` has from a distinct cause it has by participation, and
what is participated is received in the participant. -/
theorem causedPerfectionReceivedInEffect {B R : Type}
    (CausesIn : B → B → R → Prop) (ParticipatesIn : B → R → Prop)
    (ReceivedIn : B → R → B → Prop)
    (hPart : CausedByAnotherIsParticipated CausesIn ParticipatesIn)
    (hRecv : ParticipatedIsReceivedInParticipant ParticipatesIn ReceivedIn) :
    CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn := by
  sorry

/-- Target 3. If `c`'s `r` were received in its effect `x`, `c` would depend for
its being on `x`; but causing `r` in `x` is efficiently causing it, and an
efficient cause does not depend on its effect. -/
theorem causePerfectionNotReceivedInEffect {B R : Type}
    (CausesIn EfficientlyCausesIn : B → B → R → Prop) (ReceivedIn : B → R → B → Prop)
    (DependsForBeing : B → B → Prop)
    (hHaver : HaverDependsOnRecipient ReceivedIn DependsForBeing)
    (hEff : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) :
    CauseHasPerfectionNotAsReceivedInEffect CausesIn ReceivedIn := by
  sorry

/-- Target 4. An efficient cause is distinct from its effect (nothing causes
itself), the effect depends on it, and distinct things do not depend on each
other mutually. -/
theorem efficientCauseNotDependent {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
    (hAsym : DistinctBeingsNotMutuallyDependent DependsForBeing) :
    EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing := by
  sorry

/-- Target 5. Nonmutual dependence: `y` can be without `x`, `x` cannot be without
`y`, and that is the criterion of priority. -/
theorem nonmutualDependenceSuffices {B : Type}
    (PriorSimply DependsForBeing CanBeWithout : B → B → Prop)
    (hExcl : DependenceExcludesBeingWithout DependsForBeing CanBeWithout)
    (hAllow : IndependenceAllowsBeingWithout DependsForBeing CanBeWithout)
    (hCrit : PriorityByBeingWithout PriorSimply CanBeWithout) :
    NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing := by
  sorry

/-- Target 6. Everything other than the primary has participated being, what has
participated being has a distinct cause of its being, and what has its being
from another is a creature. -/
theorem othersAreCreatures {B R : Type}
    (Participated Creature : B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (p : B)
    (hOthers : OthersThanPrimaryParticipateEsse Participated p)
    (hCaused : ParticipatedHasOtherCause Participated CausesIn esse)
    (hCreature : CausedInBeingByAnotherIsCreature CausesIn Creature esse) :
    OthersAreCreaturesReading Creature p := by
  sorry

/-- Target 7. Another thing is a creature, so its esse is received, so limited;
the primary's esse is received in nothing, so (limitation only through
reception) not limited; limited esse approaches less nearly than unlimited. -/
theorem nothingElseReachesPrimary {B P D : Type} [Preorder D]
    (Creature : B → Prop) (EsseReceivedIn : B → P → Prop) (EsseLimited : B → Prop)
    (near : B → D) (p : B)
    (hOthers : OthersAreCreaturesReading Creature p)
    (hRecv : CreatureEsseIsReceived Creature EsseReceivedIn)
    (hLim : ReceivedEsseIsLimited EsseLimited EsseReceivedIn)
    (hOnly : EsseLimitedOnlyThroughReceptionReading EsseLimited EsseReceivedIn)
    (hUnrec : PrimaryEsseUnreceived EsseReceivedIn p)
    (hLess : LimitedEsseApproachesLess EsseLimited near) :
    StrictPrimacyReading near p := by
  sorry

/-- Target 8. A universal cause of being is the total cause of each other
thing's being; each perfection of that thing is a mode of its being; a total
cause of being causes each mode of it. -/
theorem universalCauseTransfers {B R : Type}
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (TotalCauseOfBeing : B → B → Prop) (ModeOfBeing : B → R → Prop)
    (hTotal : UniversalCauseOfBeingIsTotal InAct CausesIn esse TotalCauseOfBeing)
    (hModes : TotalCauseCausesModesOfBeing TotalCauseOfBeing ModeOfBeing CausesIn)
    (hPerf : PerfectionsAreModesOfBeing InAct ModeOfBeing) :
    UniversalCauseTransfersPerfections InAct CausesIn esse := by
  sorry

/-- The batch controls. -/
theorem controls : TruthCore.Causality.Round2PerfectionPrimacy.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.Round2PerfectionPrimacy
