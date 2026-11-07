module

public import TruthCore.Causality.CausalMapsBatch1

@[expose] public section

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
  intro c x r hne hc
  have hcAct : InAct c r := hHas c x r hc
  have hxLim : LimitedBy x r x := hLim x r x (hRecv c x r hne hc)
  have hcFree : ¬ LimitedBy c r x := fun h => hNot c x r hne hc (hOnly c r x h)
  exact hExceed c x r hcAct hxLim hcFree

/-- Map 1, scoped: q.4 a.2 preexistence plus the effect's having what is caused
in it gives the weak, cause-of-being version of "nothing gives what it does not
have". -/
theorem causeOfBeingHasWhatItGives {B R : Type} (CausesIn : B → B → R → Prop)
    (InAct : B → R → Prop) (esse : R)
    (hPre : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hHad : CausedPerfectionIsHad CausesIn InAct) :
    CauseOfBeingHasWhatItGives CausesIn InAct esse := by
  intro c x r hBeing hc
  have hx : InAct x r := hHad c x r hc
  exact hPre c x r hBeing hx

/-- Map 2. The effect depends on its efficient cause, the cause does not depend
on its effect, and nonmutual dependence suffices for simple priority. -/
theorem efficientCausePrior {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing)
    (hSuff : NonmutualDependenceSufficesForPriority PriorSimply DependsForBeing) :
    EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply := by
  intro c x r h
  have hxc : DependsForBeing x c := hDep c x r h
  have hcx : ¬ DependsForBeing c x := hIndep c x r h
  exact hSuff c x hxc hcx

/-- Map 2. If priority requires nonmutual dependence, nothing is prior to itself:
it would both depend and not depend on itself. -/
theorem nothingPriorToItself {B : Type} (PriorSimply DependsForBeing : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) :
    NothingPriorToItselfReading PriorSimply := by
  intro x h
  obtain ⟨hDep, hNot⟩ := hReq x x h
  exact hNot hDep

/-- Map 2, a second route that bypasses priority: from dependence of the effect
and independence of the cause, nothing is its own efficient cause. -/
theorem nothingEfficientCauseOfItself {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) :
    NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn := by
  intro x r h
  have hxx : DependsForBeing x x := hDep x x r h
  exact hIndep x x r h hxx

/-- Map 2. No mutual efficient causation: if `x` also caused `c`, `c` would
depend on `x`, which its causing `x` excludes. -/
theorem noMutualEfficientCausation {B R : Type} (EfficientlyCausesIn : B → B → R → Prop)
    (DependsForBeing : B → B → Prop)
    (hDep : EffectDependsOnEfficientCause EfficientlyCausesIn DependsForBeing)
    (hIndep : EfficientCauseNotDependentOnEffect EfficientlyCausesIn DependsForBeing) :
    NoMutualEfficientCausation EfficientlyCausesIn := by
  intro c x r s hcx hxc
  have hcDep : DependsForBeing c x := hDep x c s hxc
  exact hIndep c x r hcx hcDep

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
  have distinct : ∀ y x r, y ≠ x → MovesIn y x r → InAct y r :=
    fun y x r hne hm => hHas r y x (hMore y x r hne (hCause y x r hm))
  intro y x r hm
  rcases hEM (y = x) with hyx | hne
  · subst hyx
    obtain ⟨p, hp, hpne, hpm⟩ := hSelf y r hm
    exact hWhole p y r hp (distinct p y r hpne hpm)
  · exact distinct y x r hne hm


/-! ## Controls: each omission model and the joint witness, checked by `decide` -/

theorem causeOfQualityMoreSuch_omit_hHas : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hHas.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hHas.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfQualityMoreSuch_omit_hRecv : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hRecv.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hRecv.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfQualityMoreSuch_omit_hLim : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hLim.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hLim.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfQualityMoreSuch_omit_hOnly : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hOnly.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hOnly.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfQualityMoreSuch_omit_hNot : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hNot.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hNot.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfQualityMoreSuch_omit_hExceed : TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hExceed.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfQualityMoreSuch.omit_hExceed.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingHasWhatItGives_omit_hPre : TruthCore.Causality.CausalMapsBatch1.Control.causeOfBeingHasWhatItGives.omit_hPre.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfBeingHasWhatItGives.omit_hPre.Holds TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem causeOfBeingHasWhatItGives_omit_hHad : TruthCore.Causality.CausalMapsBatch1.Control.causeOfBeingHasWhatItGives.omit_hHad.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.causeOfBeingHasWhatItGives.omit_hHad.Holds TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem efficientCausePrior_omit_hDep : TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hDep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hDep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem efficientCausePrior_omit_hIndep : TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hIndep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hIndep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem efficientCausePrior_omit_hSuff : TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hSuff.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.efficientCausePrior.omit_hSuff.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingPriorToItself_omit_hReq : TruthCore.Causality.CausalMapsBatch1.Control.nothingPriorToItself.omit_hReq.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingPriorToItself.omit_hReq.Holds TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading
  refine ⟨?_, ?_⟩ <;> decide

theorem nothingEfficientCauseOfItself_omit_hDep : TruthCore.Causality.CausalMapsBatch1.Control.nothingEfficientCauseOfItself.omit_hDep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingEfficientCauseOfItself.omit_hDep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem nothingEfficientCauseOfItself_omit_hIndep : TruthCore.Causality.CausalMapsBatch1.Control.nothingEfficientCauseOfItself.omit_hIndep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingEfficientCauseOfItself.omit_hIndep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem noMutualEfficientCausation_omit_hDep : TruthCore.Causality.CausalMapsBatch1.Control.noMutualEfficientCausation.omit_hDep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.noMutualEfficientCausation.omit_hDep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem noMutualEfficientCausation_omit_hIndep : TruthCore.Causality.CausalMapsBatch1.Control.noMutualEfficientCausation.omit_hIndep.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.noMutualEfficientCausation.omit_hIndep.Holds TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem nothingMovesExceptInAct_omit_hCause : TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hCause.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hCause.Holds TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingMovesExceptInAct_omit_hMore : TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hMore.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hMore.Holds TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingMovesExceptInAct_omit_hHas : TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hHas.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hHas.Holds TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingMovesExceptInAct_omit_hSelf : TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hSelf.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hSelf.Holds TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem nothingMovesExceptInAct_omit_hWhole : TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hWhole.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.nothingMovesExceptInAct.omit_hWhole.Holds TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witness_holds : TruthCore.Causality.CausalMapsBatch1.Control.witness.Holds := by
  delta TruthCore.Causality.CausalMapsBatch1.Control.witness.Holds TruthCore.Causality.CausalMapsBatch1.CauseHasPerfectionNotAsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.CauseHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CauseOfBeingHasWhatItGives TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsHad TruthCore.Causality.CausalMapsBatch1.CausedPerfectionIsReceivedInEffect TruthCore.Causality.CausalMapsBatch1.EffectDependsOnEfficientCause TruthCore.Causality.CausalMapsBatch1.EfficientCauseNotDependentOnEffect TruthCore.Causality.CausalMapsBatch1.MoverCausesWhatItMovesTo TruthCore.Causality.CausalMapsBatch1.NoMutualEfficientCausation TruthCore.Causality.CausalMapsBatch1.NonmutualDependenceSufficesForPriority TruthCore.Causality.CausalMapsBatch1.PerfectionLimitedOnlyThroughReception TruthCore.Causality.CausalMapsBatch1.PriorityRequiresNonmutualDependence TruthCore.Causality.CausalMapsBatch1.ReceivedPerfectionIsLimitedByRecipient TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart TruthCore.Causality.CausalMapsBatch1.UnlimitedPossessionExceedsLimited TruthCore.Causality.CausalMapsBatch1.WholeInActThroughItsPart TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading TruthCore.Latin.Aquinas.SummaTheologiae.EfficientCauseIsPriorToEffectReading TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading TruthCore.Latin.Aquinas.SummaTheologiae.NothingIsEfficientCauseOfItselfReading TruthCore.Latin.Aquinas.SummaTheologiae.NothingPriorToItselfReading TruthCore.Latin.Aquinas.SummaTheologiae.PerfectionsOfEffectPreexistInCauseReading
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide


/-- The batch controls. -/
theorem controls : TruthCore.Causality.CausalMapsBatch1.Control.Certificate :=
  ⟨causeOfQualityMoreSuch_omit_hHas,
   causeOfQualityMoreSuch_omit_hRecv,
   causeOfQualityMoreSuch_omit_hLim,
   causeOfQualityMoreSuch_omit_hOnly,
   causeOfQualityMoreSuch_omit_hNot,
   causeOfQualityMoreSuch_omit_hExceed,
   causeOfBeingHasWhatItGives_omit_hPre,
   causeOfBeingHasWhatItGives_omit_hHad,
   efficientCausePrior_omit_hDep,
   efficientCausePrior_omit_hIndep,
   efficientCausePrior_omit_hSuff,
   nothingPriorToItself_omit_hReq,
   nothingEfficientCauseOfItself_omit_hDep,
   nothingEfficientCauseOfItself_omit_hIndep,
   noMutualEfficientCausation_omit_hDep,
   noMutualEfficientCausation_omit_hIndep,
   nothingMovesExceptInAct_omit_hCause,
   nothingMovesExceptInAct_omit_hMore,
   nothingMovesExceptInAct_omit_hHas,
   nothingMovesExceptInAct_omit_hSelf,
   nothingMovesExceptInAct_omit_hWhole,
   witness_holds⟩

end TruthCore.Results.Causality.CausalMapsBatch1
