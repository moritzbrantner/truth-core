import TruthCore.Causality.TermSenseForks2

/-! Sense forks, batch 2: "uniting cause" and "in act". Joint theorems in which
exclusivity carries the step to an existing root-route node, per-sense
branches, strength order, and controls. Analyst formulations, attribution
deferred. -/

namespace TruthCore.Results.Causality.TermSenseForks2

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.TermSenseForks

/-! ## "uniting cause" -/

/-- Joint sense fork for the uniting-cause step. Whichever single sense the
route's "causes" has (coverage for both uses, exclusivity of the reading), the
uniter causes the composite and nothing causes itself in that one sense, so the
uniter is distinct from the composite; with the uniter causing the composite's
being, every composite has a distinct cause of its being. -/
theorem compositeUnitingCauseBySenseFork {Being Respect : Type}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (F : UnitingFrame Being Respect) (Select : UnitingSense → Prop)
    (use : UnitingUse → Being → Being → Prop)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnited : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf F.Unites)
    (hBeing : UnitingCauseCausesBeingReading F.Unites F.CausesIn F.esse)
    (hCover : UnitingCauseSensesExhaustive F Select use)
    (hUnique : UnitingCauseSenseUnique Select)
    (hUniter : UniterCausesInRouteSense F use)
    (hNoSelf : NothingCausesItselfInRouteUse use) :
    CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse := by
  sorry

/-- The being branch: if nothing causes its own being, the uniter, which causes
the composite's being, is distinct from it. This route needs neither the
efficient-cause bridge nor the secunda via's no-self-causation premise. -/
theorem compositeUnitingCauseFromOwnBeing {Being Respect : Type}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnited : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites)
    (hBeing : UnitingCauseCausesBeingReading Unites CausesIn esse)
    (hOwn : NothingCausesItsOwnBeing CausesIn esse) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse := by
  sorry

/-- The uniting branch: if nothing unites components into itself, the uniter is
distinct from the composite. -/
theorem compositeUnitingCauseFromNoSelfUniting {Being Respect : Type}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop)
    (Unites : Being → Being → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hTwo : CompositeHasTwoDistinctComponentsReading Composite ComponentOf)
    (hUnited : DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf Unites)
    (hBeing : UnitingCauseCausesBeingReading Unites CausesIn esse)
    (hNoSelf : NothingUnitesItself Unites) :
    CompositeHasAUnitingCauseReading Composite CausesIn esse := by
  sorry

/-- Strength order: nothing causes a perfection in itself implies nothing
causes its own being (the instance r = esse). The strong version is refuted
under STMT-SOME-SUBJECT-CAUSES-ITS-OWN-PERFECTION; the weak one is not. -/
theorem nothingCausesItsOwnBeingFromPerfection {Being Respect : Type}
    (F : CauseFrame Being Respect) (esse : Respect)
    (hAll : NothingCausesItsOwnPerfection F) :
    NothingCausesItsOwnBeing F.CausesIn esse := by
  sorry

/-! ## "in act" -/

/-- Joint sense fork for the prima via step. Whichever single sense "in act"
has (coverage for both uses, exclusivity of the reading), a thing moved in a
respect is in potency there, a mover is in act there in that sense, and nothing
is in act in that sense and in potency in the same respect; so nothing moves
itself in a respect in which it is being moved. -/
theorem noSelfMotionByActSenseFork {Being Respect : Type}
    (F : ActFrame Being Respect) (Select : ActSense → Prop)
    (use : ActUse → Being → Respect → Prop)
    (hCover : InActSensesExhaustive F Select use)
    (hUnique : InActSenseUnique Select)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsInActReading F.MovesIn (use .moverInAct))
    (hNon : NotActAndPotencyInSameRespectReading (use .nonSimultaneity) F.InPotency) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn := by
  sorry

/-- The formal branch (IN-ACT_1). -/
theorem noSelfMotionFormally {Being Respect : Type} (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsFormallyInAct F)
    (hNon : NothingFormallyInActAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn := by
  sorry

/-- The virtual branch (IN-ACT_2). -/
theorem noSelfMotionVirtually {Being Respect : Type} (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsVirtuallyInAct F)
    (hNon : NothingVirtuallyInActAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn := by
  sorry

/-- The formal-or-virtual branch (IN-ACT_3). -/
theorem noSelfMotionFormallyOrVirtually {Being Respect : Type}
    (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsInActFormallyOrVirtually F)
    (hNon : NothingInActFormallyOrVirtuallyAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn := by
  sorry

/-- Strength order: moving only as formally in act implies moving only as in
act formally or virtually. -/
theorem movesAsInActInclusiveFromFormal {Being Respect : Type}
    (F : ActFrame Being Respect) (h : MovesOnlyAsFormallyInAct F) :
    MovesOnlyAsInActFormallyOrVirtually F := by
  sorry

/-- Strength order: inclusive non-simultaneity implies formal non-simultaneity. -/
theorem nonSimultaneityFormalFromInclusive {Being Respect : Type}
    (F : ActFrame Being Respect) (h : NothingInActFormallyOrVirtuallyAndInPotency F) :
    NothingFormallyInActAndInPotency F := by
  sorry

/-! ## Cause of becoming or of being -/

/-- BECOMING-BEING-CAUSE_2 route: participated beings have esse distinct from
essence (open bridge), and by ST I q.3 a.4 such esse has an actual external
efficient cause. -/
theorem participatedExternalEsseCause {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect)
    (hDistinct : ParticipatedHasDistinctEsse F)
    (hExternal : PrimaPars.Question3.Article4.DistinctEsseRequiresExternalCauseReading
      F.profile) :
    ParticipatedHasExternalEsseCause F := by
  sorry

/-- Sense bridge BECOMING-BEING-CAUSE_2 → BECOMING-BEING-CAUSE_3: an external
efficient cause of esse is another being that causes the thing's being, so
the participated has another cause of its being (the root-path statement). -/
theorem participatedHasOtherCauseFromExternal {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect)
    (h : ParticipatedHasExternalEsseCause F) :
    TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause
      F.Participated F.profile.CausesIn F.profile.esse := by
  sorry

/-! ## Controls -/

theorem controls : TermSenseForks2Controls := by
  sorry

end TruthCore.Results.Causality.TermSenseForks2
