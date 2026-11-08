module

public import TruthCore.Causality.Round2PerfectionPrimacy

@[expose] public section

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
  intro c x r hc hx hcx
  have h1 : deg x r ≤ cap x r := hWithin x r x hx
  have h2 : cap x r < deg c r := hBeyond c r x hc hcx
  exact hMore r c x (lt_of_le_of_lt h1 h2)

/-- Target 2. What `x` has from a distinct cause it has by participation, and
what is participated is received in the participant. -/
theorem causedPerfectionReceivedInEffect {B R : Type}
    (CausesIn : B → B → R → Prop) (ParticipatesIn : B → R → Prop)
    (ReceivedIn : B → R → B → Prop)
    (hPart : CausedByAnotherIsParticipated CausesIn ParticipatesIn)
    (hRecv : ParticipatedIsReceivedInParticipant ParticipatesIn ReceivedIn) :
    CausedPerfectionIsReceivedInEffect CausesIn ReceivedIn := by
  intro c x r hne hc
  have hp : ParticipatesIn x r := hPart c x r hne hc
  exact hRecv x r hp

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
  intro c x r hne hc hrec
  have hd : DependsForBeing c x := hHaver c r x hrec
  have he : EfficientlyCausesIn c x r := hEff c x r hne hc
  exact hIndep c x r he hd

/-- Target 4. An efficient cause is distinct from its effect (nothing causes
itself), the effect depends on it, and distinct things do not depend on each
other mutually. -/
theorem efficientCauseNotDependent {B R : Type}
    (EfficientlyCausesIn : B → B → R → Prop) (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn)
    (hAsym : DistinctBeingsNotMutuallyDependent DependsForBeing) :
    EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing := by
  intro c x r h
  have hne : x ≠ c := fun e => hNoSelf x r (by subst e; exact h)
  have hxc : DependsForBeing x c := hDep c x r h
  exact hAsym x c hne hxc

/-- Target 5. Nonmutual dependence: `y` can be without `x`, `x` cannot be without
`y`, and that is the criterion of priority. -/
theorem nonmutualDependenceSuffices {B : Type}
    (PriorSimply DependsForBeing CanBeWithout : B → B → Prop)
    (hExcl : DependenceExcludesBeingWithout DependsForBeing CanBeWithout)
    (hAllow : IndependenceAllowsBeingWithout DependsForBeing CanBeWithout)
    (hCrit : PriorityByBeingWithout PriorSimply CanBeWithout) :
    NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing := by
  intro y x hxy hyx
  have hy : CanBeWithout y x := hAllow y x hyx
  have hx : ¬ CanBeWithout x y := hExcl x y hxy
  exact hCrit y x hy hx

/-- Target 6. Everything other than the primary has participated being, what has
participated being has a distinct cause of its being, and what has its being
from another is a creature. -/
theorem othersAreCreatures {B R : Type}
    (Participated Creature : B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (p : B)
    (hOthers : OthersThanPrimaryParticipateEsse Participated p)
    (hCaused : ParticipatedHasOtherCause Participated CausesIn esse)
    (hCreature : CausedInBeingByAnotherIsCreature CausesIn Creature esse) :
    OthersAreCreaturesReading Creature p := by
  intro x hx
  obtain ⟨c, hne, hc⟩ := hCaused x (hOthers x hx)
  exact hCreature c x hne hc

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
  intro x hx
  obtain ⟨z, hz⟩ := hRecv x (hOthers x hx)
  have hxl : EsseLimited x := hLim x z hz
  have hpl : ¬ EsseLimited p := fun h => by
    obtain ⟨z', hz'⟩ := hOnly p h
    exact hUnrec z' hz'
  exact hLess x p hxl hpl

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
  intro c hc x r hne hcx hx
  have ht : TotalCauseOfBeing c x := hTotal c hc x hne hcx
  have hm : ModeOfBeing x r := hPerf x r hx
  exact hModes c x r ht hm

theorem causePerfectionNotReceivedInEffect_omit_hHaver : TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hHaver.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hHaver.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem causePerfectionNotReceivedInEffect_omit_hEff : TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hEff.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hEff.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem causePerfectionNotReceivedInEffect_omit_hIndep : TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hIndep.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.causePerfectionNotReceivedInEffect.omit_hIndep.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem causedPerfectionReceivedInEffect_omit_hPart : TruthCore.Causality.Round2PerfectionPrimacy.Control.causedPerfectionReceivedInEffect.omit_hPart.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.causedPerfectionReceivedInEffect.omit_hPart.Holds TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem causedPerfectionReceivedInEffect_omit_hRecv : TruthCore.Causality.Round2PerfectionPrimacy.Control.causedPerfectionReceivedInEffect.omit_hRecv.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.causedPerfectionReceivedInEffect.omit_hRecv.Holds TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem efficientCauseNotDependent_omit_hDep : TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hDep.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hDep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem efficientCauseNotDependent_omit_hNoSelf : TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hNoSelf.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hNoSelf.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem efficientCauseNotDependent_omit_hAsym : TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hAsym.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.efficientCauseNotDependent.omit_hAsym.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nonmutualDependenceSuffices_omit_hExcl : TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hExcl.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hExcl.Holds TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nonmutualDependenceSuffices_omit_hAllow : TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hAllow.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hAllow.Holds TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nonmutualDependenceSuffices_omit_hCrit : TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hCrit.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nonmutualDependenceSuffices.omit_hCrit.Holds TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem othersAreCreatures_omit_hOthers : TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hOthers.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hOthers.Holds TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem othersAreCreatures_omit_hCaused : TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hCaused.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hCaused.Holds TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem othersAreCreatures_omit_hCreature : TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hCreature.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.othersAreCreatures.omit_hCreature.Holds TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

set_option synthInstance.maxSize 1024 in
theorem universalCauseTransfers_omit_hTotal : TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hTotal.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hTotal.Holds TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

set_option synthInstance.maxSize 1024 in
theorem universalCauseTransfers_omit_hModes : TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hModes.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hModes.Holds TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

set_option synthInstance.maxSize 1024 in
theorem universalCauseTransfers_omit_hPerf : TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hPerf.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.universalCauseTransfers.omit_hPerf.Holds TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem unlimitedPossessionExceedsLimited_omit_hWithin : TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hWithin.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hWithin.Holds TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem unlimitedPossessionExceedsLimited_omit_hBeyond : TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hBeyond.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hBeyond.Holds TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem unlimitedPossessionExceedsLimited_omit_hMore : TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hMore.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.unlimitedPossessionExceedsLimited.omit_hMore.Holds TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hOthers : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hOthers.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hOthers.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hRecv : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hRecv.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hRecv.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hLim : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hLim.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hLim.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hOnly : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hOnly.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hOnly.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hUnrec : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hUnrec.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hUnrec.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingElseReachesPrimary_omit_hLess : TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hLess.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.nothingElseReachesPrimary.omit_hLess.Holds TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option synthInstance.maxSize 1024 in
theorem witness_holds : TruthCore.Causality.Round2PerfectionPrimacy.Control.witness.Holds := by
  delta TruthCore.Causality.Round2PerfectionPrimacy.Control.witness.Holds TruthCore.Case.Catholicism.UniversalCauseTransfersPerfections TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause TruthCore.Causality.ReceptionLimitation.ReceivedEsseIsLimited TruthCore.Causality.Round2PerfectionPrimacy.CausedByAnotherIsParticipated TruthCore.Causality.Round2PerfectionPrimacy.CausedInBeingByAnotherIsCreature TruthCore.Causality.Round2PerfectionPrimacy.CreatureEsseIsReceived TruthCore.Causality.Round2PerfectionPrimacy.DependenceExcludesBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent TruthCore.Causality.Round2PerfectionPrimacy.GreaterDegreeIsMore TruthCore.Causality.Round2PerfectionPrimacy.HaverDependsOnRecipient TruthCore.Causality.Round2PerfectionPrimacy.IndependenceAllowsBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.LimitedEsseApproachesLess TruthCore.Causality.Round2PerfectionPrimacy.LimitedHavingIsWithinCapacity TruthCore.Causality.Round2PerfectionPrimacy.OthersThanPrimaryParticipateEsse TruthCore.Causality.Round2PerfectionPrimacy.ParticipatedIsReceivedInParticipant TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient TruthCore.Causality.Round2PerfectionPrimacy.PerfectionsAreModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.PrimaryEsseUnreceived TruthCore.Causality.Round2PerfectionPrimacy.PriorityByBeingWithout TruthCore.Causality.Round2PerfectionPrimacy.TotalCauseCausesModesOfBeing TruthCore.Causality.Round2PerfectionPrimacy.UniversalCauseOfBeingIsTotal TruthCore.Causality.Round2PerfectionPrimacy.UnlimitedHavingExceedsCapacity TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading TruthCore.Latin.Aquinas.SummaTheologiae.OthersAreCreaturesReading TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception.EsseLimitedOnlyThroughReceptionReading TruthCore.Latin.Aquinas.SummaTheologiae.StrictPrimacyReading TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus
  decide

/-- The batch controls. -/
theorem controls : TruthCore.Causality.Round2PerfectionPrimacy.Control.Certificate :=
  ⟨causePerfectionNotReceivedInEffect_omit_hHaver,
   causePerfectionNotReceivedInEffect_omit_hEff,
   causePerfectionNotReceivedInEffect_omit_hIndep,
   causedPerfectionReceivedInEffect_omit_hPart,
   causedPerfectionReceivedInEffect_omit_hRecv,
   efficientCauseNotDependent_omit_hDep,
   efficientCauseNotDependent_omit_hNoSelf,
   efficientCauseNotDependent_omit_hAsym,
   nonmutualDependenceSuffices_omit_hExcl,
   nonmutualDependenceSuffices_omit_hAllow,
   nonmutualDependenceSuffices_omit_hCrit,
   othersAreCreatures_omit_hOthers,
   othersAreCreatures_omit_hCaused,
   othersAreCreatures_omit_hCreature,
   universalCauseTransfers_omit_hTotal,
   universalCauseTransfers_omit_hModes,
   universalCauseTransfers_omit_hPerf,
   unlimitedPossessionExceedsLimited_omit_hWithin,
   unlimitedPossessionExceedsLimited_omit_hBeyond,
   unlimitedPossessionExceedsLimited_omit_hMore,
   nothingElseReachesPrimary_omit_hOthers,
   nothingElseReachesPrimary_omit_hRecv,
   nothingElseReachesPrimary_omit_hLim,
   nothingElseReachesPrimary_omit_hOnly,
   nothingElseReachesPrimary_omit_hUnrec,
   nothingElseReachesPrimary_omit_hLess,
   witness_holds⟩

end TruthCore.Results.Causality.Round2PerfectionPrimacy
