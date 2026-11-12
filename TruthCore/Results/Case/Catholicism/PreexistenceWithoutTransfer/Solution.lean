module

public import TruthCore.Case.Catholicism.PreexistenceWithoutTransfer

@[expose] public section

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
  intro c x hne hc
  have hcAct : InAct c esse := hHas c x hc
  have hxLim : LimitedBy x esse x := hLim x esse x (hRecv c x esse hne hc)
  have hcFree : ¬ LimitedBy c esse x := fun h => hNot c x esse hne hc (hOnly c esse x h)
  exact hExceed c x esse hcAct hxLim hcFree

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
  intro g hg
  obtain ⟨y, hy⟩ := hOther g hg
  refine ⟨hHas esse g y (hMore g y (fun h => hy h.symm) (hCauses g y hg hy)), ?_⟩
  intro z hz
  rcases hEM (z = g) with hEq | hNe
  · subst hEq
    exact hAsym esse z z hz hz
  · exact hAsym esse g z (hMore g z (fun h => hNe h.symm) (hCauses g z hg hNe)) hz

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
  obtain ⟨m, hMax, hCauses⟩ := hMaxime
  have hUnique : ∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m := by
    intro m' hMax'
    rcases hEM (m' = m) with h | hne
    · exact h
    · exact absurd (hCauseMore m m' (fun h => hne h.symm) (hCauses m' hne hMax'.1))
        (hMax'.2 m)
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hPerfections m x r (hCauses x hOther (hBeing x r hAct)) hAct
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent (hFirstBeing m hMax)
  exact ⟨m, hFull m hMax hCauses hEvery hRemote hUnique⟩

/-- Q.4 a.2 preexistence from transfer and the cause-of-being restriction: a
cause of `x`'s being causes each perfection `x` has, and a cause of a thing's
being has every perfection it causes in it. -/
theorem preexistOfTransferAndRestriction {B R : Type} (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hTransfer : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hGives : CauseOfBeingHasWhatItGives CausesIn InAct esse) :
    PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse := by
  intro c x r hc hx
  exact hGives c x r hc (hTransfer c x r hc hx)

/-- "More such" carries distinct-cause transfer: a distinct cause of `r` in `x`
is more `r` than `x`, and what is more `r` has `r`. -/
theorem distinctCauseGivesOfMoreSuch {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn) :
    DistinctCauseHasWhatItGives CausesIn InAct := by
  intro c x r hne hc
  exact hHas r c x (hMore c x r hne hc)

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
  intro c x r hne hc
  have hcAct : InAct c r := hHas c x r hne hc
  have hxLim : LimitedBy x r x := hLim x r x (hRecv c x r hne hc)
  have hcFree : ¬ LimitedBy c r x := fun h => hNot c x r hne hc (hOnly c r x h)
  exact hExceed c x r hcAct hxLim hcFree

/-- Strength order: "more such" entails its esse instance. -/
theorem moreInBeingOfMoreSuch {B R : Type} (CausesIn : B → B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (h : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    CauseOfBeingIsMoreInBeing CausesIn MoreIn esse :=
  fun c x hne hc => h c x esse hne hc

/-- Strength order: the unrestricted principle entails distinct-cause transfer. -/
theorem distinctCauseGivesOfCauseGives {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop)
    (h : TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives CausesIn InAct) :
    DistinctCauseHasWhatItGives CausesIn InAct :=
  fun c x r _ hc => h c x r hc

/-! ## Omission models and joint witnesses -/

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

theorem causeOfBeingMoreInBeing_omit_hHas : Control.causeOfBeingMoreInBeing.omit_hHas.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hHas.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_omit_hRecv : Control.causeOfBeingMoreInBeing.omit_hRecv.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hRecv.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_omit_hLim : Control.causeOfBeingMoreInBeing.omit_hLim.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hLim.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_omit_hOnly : Control.causeOfBeingMoreInBeing.omit_hOnly.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hOnly.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_omit_hNot : Control.causeOfBeingMoreInBeing.omit_hNot.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hNot.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_omit_hExceed : Control.causeOfBeingMoreInBeing.omit_hExceed.Holds := by
  delta Control.causeOfBeingMoreInBeing.omit_hExceed.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingMoreInBeing_witness : Control.causeOfBeingMoreInBeing.witness.Holds := by
  delta Control.causeOfBeingMoreInBeing.witness.Holds TruthCore.Case.Catholicism.CauseOfBeingHasBeing.CauseOfBeingInActAsToBeing TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem distinctCauseGivesOfMoreSuch_omit_hMore : Control.distinctCauseGivesOfMoreSuch.omit_hMore.Holds := by
  delta Control.distinctCauseGivesOfMoreSuch.omit_hMore.Holds TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem distinctCauseGivesOfMoreSuch_omit_hHas : Control.distinctCauseGivesOfMoreSuch.omit_hHas.Holds := by
  delta Control.distinctCauseGivesOfMoreSuch.omit_hHas.Holds TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem distinctCauseGivesOfMoreSuch_witness : Control.distinctCauseGivesOfMoreSuch.witness.Holds := by
  delta Control.distinctCauseGivesOfMoreSuch.witness.Holds TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide
theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hMaxime : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hMaxime.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hMaxime.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hBeing : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hBeing.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hBeing.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hCauseMore : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hCauseMore.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hCauseMore.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hPerfections : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hPerfections.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hPerfections.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hNoComponent : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hNoComponent.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hNoComponent.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hFirstBeing : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hFirstBeing.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hFirstBeing.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_omit_hFull : Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hFull.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.omit_hFull.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godExistsFromMaximeEnsCausingAllByBeing_witness : Control.godExistsFromMaximeEnsCausingAllByBeing.witness.Holds := by
  delta Control.godExistsFromMaximeEnsCausingAllByBeing.witness.Holds TruthCore.Latin.Aquinas.SummaTheologiae.MaximeEnsCausesBeingOfAllReading TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus TruthCore.Latin.Aquinas.SummaTheologiae.ActualityOnlyInsofarAsBeingReading TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Latin.Aquinas.SummaTheologiae.NoComponentIsFirstBeingReading TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing TruthCore.Case.Catholicism.GodNamesTheFullyDescribedPrinciple TruthCore.Case.Catholicism.CausesEveryPerfectionOfOthers TruthCore.Case.Catholicism.RemoteFromAll TruthCore.Case.Catholicism.GodExists
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem godMaximalFromCausingBeing_omit_hCauses : Control.godMaximalFromCausingBeing.omit_hCauses.Holds := by
  delta Control.godMaximalFromCausingBeing.omit_hCauses.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godMaximalFromCausingBeing_omit_hMore : Control.godMaximalFromCausingBeing.omit_hMore.Holds := by
  delta Control.godMaximalFromCausingBeing.omit_hMore.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godMaximalFromCausingBeing_omit_hHas : Control.godMaximalFromCausingBeing.omit_hHas.Holds := by
  delta Control.godMaximalFromCausingBeing.omit_hHas.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godMaximalFromCausingBeing_omit_hAsym : Control.godMaximalFromCausingBeing.omit_hAsym.Holds := by
  delta Control.godMaximalFromCausingBeing.omit_hAsym.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godMaximalFromCausingBeing_omit_hOther : Control.godMaximalFromCausingBeing.omit_hOther.Holds := by
  delta Control.godMaximalFromCausingBeing.omit_hOther.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem godMaximalFromCausingBeing_witness : Control.godMaximalFromCausingBeing.witness.Holds := by
  delta Control.godMaximalFromCausingBeing.witness.Holds TruthCore.Causality.GodMaximalCausal.GodCausesBeingOfAllOthers TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.CauseOfBeingIsMoreInBeing TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric TruthCore.Causality.GodMaximalCausal.SomethingOtherThanGodExists TruthCore.Case.Catholicism.GodIsMaximalInBeing TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem moreSuchOfDistinctCauseGives_omit_hHas : Control.moreSuchOfDistinctCauseGives.omit_hHas.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hHas.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_omit_hRecv : Control.moreSuchOfDistinctCauseGives.omit_hRecv.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hRecv.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_omit_hLim : Control.moreSuchOfDistinctCauseGives.omit_hLim.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hLim.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_omit_hOnly : Control.moreSuchOfDistinctCauseGives.omit_hOnly.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hOnly.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_omit_hNot : Control.moreSuchOfDistinctCauseGives.omit_hNot.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hNot.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_omit_hExceed : Control.moreSuchOfDistinctCauseGives.omit_hExceed.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.omit_hExceed.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem moreSuchOfDistinctCauseGives_witness : Control.moreSuchOfDistinctCauseGives.witness.Holds := by
  delta Control.moreSuchOfDistinctCauseGives.witness.Holds TruthCore.Case.Catholicism.PreexistenceWithoutTransfer.DistinctCauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem preexistOfTransferAndRestriction_omit_hTransfer : Control.preexistOfTransferAndRestriction.omit_hTransfer.Holds := by
  delta Control.preexistOfTransferAndRestriction.omit_hTransfer.Holds TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem preexistOfTransferAndRestriction_omit_hGives : Control.preexistOfTransferAndRestriction.omit_hGives.Holds := by
  delta Control.preexistOfTransferAndRestriction.omit_hGives.Holds TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem preexistOfTransferAndRestriction_witness : Control.preexistOfTransferAndRestriction.witness.Holds := by
  delta Control.preexistOfTransferAndRestriction.witness.Holds TruthCore.Case.Catholicism.CauseOfBeingCausesEveryPerfection TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The strictness and nonvacuity controls hold. -/
theorem strictness : Control.Strictness := by
  unfold Control.Strictness
  delta CauseOfBeingIsMoreInBeing DistinctCauseHasWhatItGives CauseOfQualityInAnotherIsMoreSuchReading
    CauseOfBeingHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives
    CauseOfBeingInActAsToBeing CausedPerfectionIsReceivedInEffect ReceivedPerfectionIsLimitedByRecipient
    PerfectionLimitedOnlyThroughReception CauseHasPerfectionNotAsReceivedInEffect
    UnlimitedPossessionExceedsLimited CauseOfBeingCausesEveryPerfection
    PerfectionsOfEffectPreexistInCauseReading Control.causesBeing Control.causesAll Control.causesOther
    Control.moreFalse Control.recvTrue Control.moreEsseOnly Control.esse
    GodCausesBeingOfAllOthers MoreInIsAsymmetric SomethingOtherThanGodExists
    MoreSuchHasThePerfectionReading GodIsMaximalInBeing IsMaximumIn
    TruthCore.Causality.GodMaximalCausal.Control.isGod TruthCore.Causality.GodMaximalCausal.Control.causes
    TruthCore.Causality.GodMaximalCausal.Control.more TruthCore.Causality.GodMaximalCausal.Control.inAct
  and_intros <;> decide

/-- The finite controls hold. -/
theorem controls : Control.Controls :=
  ⟨strictness, causeOfBeingMoreInBeing_omit_hHas, causeOfBeingMoreInBeing_omit_hRecv, causeOfBeingMoreInBeing_omit_hLim, causeOfBeingMoreInBeing_omit_hOnly, causeOfBeingMoreInBeing_omit_hNot, causeOfBeingMoreInBeing_omit_hExceed, causeOfBeingMoreInBeing_witness, distinctCauseGivesOfMoreSuch_omit_hMore, distinctCauseGivesOfMoreSuch_omit_hHas, distinctCauseGivesOfMoreSuch_witness, godExistsFromMaximeEnsCausingAllByBeing_omit_hMaxime, godExistsFromMaximeEnsCausingAllByBeing_omit_hBeing, godExistsFromMaximeEnsCausingAllByBeing_omit_hCauseMore, godExistsFromMaximeEnsCausingAllByBeing_omit_hPerfections, godExistsFromMaximeEnsCausingAllByBeing_omit_hNoComponent, godExistsFromMaximeEnsCausingAllByBeing_omit_hFirstBeing, godExistsFromMaximeEnsCausingAllByBeing_omit_hFull, godExistsFromMaximeEnsCausingAllByBeing_witness, godMaximalFromCausingBeing_omit_hCauses, godMaximalFromCausingBeing_omit_hMore, godMaximalFromCausingBeing_omit_hHas, godMaximalFromCausingBeing_omit_hAsym, godMaximalFromCausingBeing_omit_hOther, godMaximalFromCausingBeing_witness, moreSuchOfDistinctCauseGives_omit_hHas, moreSuchOfDistinctCauseGives_omit_hRecv, moreSuchOfDistinctCauseGives_omit_hLim, moreSuchOfDistinctCauseGives_omit_hOnly, moreSuchOfDistinctCauseGives_omit_hNot, moreSuchOfDistinctCauseGives_omit_hExceed, moreSuchOfDistinctCauseGives_witness, preexistOfTransferAndRestriction_omit_hTransfer, preexistOfTransferAndRestriction_omit_hGives, preexistOfTransferAndRestriction_witness⟩

end TruthCore.Results.Case.Catholicism.PreexistenceWithoutTransfer
