module

public import TruthCore.Causality.TermSenseForks2

/-! Sense forks, batch 2: "uniting cause" and "in act". Joint theorems in which
exclusivity carries the step to an existing root-route node, per-sense
branches, strength order, and controls. Analyst formulations, attribution
deferred. -/

@[expose] public section

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
  have hAgree : UsesAgree use :=
    usesAgree_of_cover_unique F.CausesBy Select use hCover hUnique
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ := hTwo x hx
  obtain ⟨c, hc⟩ := hUnited x a b ha hb hab
  refine ⟨c, ?_, hBeing c a b x hc⟩
  intro hcx
  subst hcx
  have h1 : use .uniterCauses c c := hUniter c a b c hc
  rw [hAgree .uniterCauses .noSelfCause] at h1
  exact hNoSelf c h1

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
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ := hTwo x hx
  obtain ⟨c, hc⟩ := hUnited x a b ha hb hab
  have hCause : CausesIn c x esse := hBeing c a b x hc
  refine ⟨c, ?_, hCause⟩
  intro hcx
  subst hcx
  exact hOwn c hCause

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
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ := hTwo x hx
  obtain ⟨c, hc⟩ := hUnited x a b ha hb hab
  refine ⟨c, ?_, hBeing c a b x hc⟩
  intro hcx
  subst hcx
  exact hNoSelf c a b hc

/-- Strength order: nothing causes a perfection in itself implies nothing
causes its own being (the instance r = esse). The strong version is refuted
under STMT-SOME-SUBJECT-CAUSES-ITS-OWN-PERFECTION; the weak one is not. -/
theorem nothingCausesItsOwnBeingFromPerfection {Being Respect : Type}
    (F : CauseFrame Being Respect) (esse : Respect)
    (hAll : NothingCausesItsOwnPerfection F) :
    NothingCausesItsOwnBeing F.CausesIn esse :=
  fun x => hAll x esse

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
  have hAgree : UsesAgree use :=
    usesAgree_of_cover_unique F.InActBy Select use hCover hUnique
  intro x r hMoved hMoves
  have h1 : use .moverInAct x r := hAct x x r hMoves
  rw [hAgree .moverInAct .nonSimultaneity] at h1
  exact hNon x r ⟨h1, hPot x r hMoved⟩

/-- The formal branch (IN-ACT_1). -/
theorem noSelfMotionFormally {Being Respect : Type} (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsFormallyInAct F)
    (hNon : NothingFormallyInActAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn :=
  fun x r hMoved hMoves => hNon x r ⟨hAct x x r hMoves, hPot x r hMoved⟩

/-- The virtual branch (IN-ACT_2). -/
theorem noSelfMotionVirtually {Being Respect : Type} (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsVirtuallyInAct F)
    (hNon : NothingVirtuallyInActAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn :=
  fun x r hMoved hMoves => hNon x r ⟨hAct x x r hMoves, hPot x r hMoved⟩

/-- The formal-or-virtual branch (IN-ACT_3). -/
theorem noSelfMotionFormallyOrVirtually {Being Respect : Type}
    (F : ActFrame Being Respect)
    (hPot : MovedOnlyAsInPotencyReading F.MovedIn F.InPotency)
    (hAct : MovesOnlyAsInActFormallyOrVirtually F)
    (hNon : NothingInActFormallyOrVirtuallyAndInPotency F) :
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn :=
  fun x r hMoved hMoves => hNon x r ⟨hAct x x r hMoves, hPot x r hMoved⟩

/-- Strength order: moving only as formally in act implies moving only as in
act formally or virtually. -/
theorem movesAsInActInclusiveFromFormal {Being Respect : Type}
    (F : ActFrame Being Respect) (h : MovesOnlyAsFormallyInAct F) :
    MovesOnlyAsInActFormallyOrVirtually F :=
  fun y x r hm => Or.inl (h y x r hm)

/-- Strength order: inclusive non-simultaneity implies formal non-simultaneity. -/
theorem nonSimultaneityFormalFromInclusive {Being Respect : Type}
    (F : ActFrame Being Respect) (h : NothingInActFormallyOrVirtuallyAndInPotency F) :
    NothingFormallyInActAndInPotency F :=
  fun x r hb => h x r ⟨Or.inl hb.1, hb.2⟩

/-! ## Cause of becoming or of being -/

/-- BECOMING-BEING-CAUSE_2 route: participated beings have esse distinct from
essence (open bridge), and by ST I q.3 a.4 such esse has an actual external
efficient cause. -/
theorem participatedExternalEsseCause {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect)
    (hDistinct : ParticipatedHasDistinctEsse F)
    (hExternal : PrimaPars.Question3.Article4.DistinctEsseRequiresExternalCauseReading
      F.profile) :
    ParticipatedHasExternalEsseCause F :=
  fun x hx => hExternal x (hDistinct x hx)

/-- Sense bridge BECOMING-BEING-CAUSE_2 → BECOMING-BEING-CAUSE_3: an external
efficient cause of esse is another being that causes the thing's being, so
the participated has another cause of its being (the root-path statement). -/
theorem participatedHasOtherCauseFromExternal {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect)
    (h : ParticipatedHasExternalEsseCause F) :
    TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause
      F.Participated F.profile.CausesIn F.profile.esse := by
  intro x hx
  obtain ⟨y, hne, _, hc⟩ := h x hx
  exact ⟨y, hne, hc⟩

/-! ## Controls -/

/-- Uniting frame over `Bool`: `true` is the composite; `uniter` unites any
components into it and causes its being. -/
abbrev uf (uniter : Bool) : UnitingFrame Bool Unit :=
  ⟨fun c _ _ x => c = uniter ∧ x = true, fun _ _ _ => False,
    fun c x _ => c = uniter ∧ x = true, ()⟩

/-- The uses read in two given senses. -/
abbrev uuse (F : UnitingFrame Bool Unit) (σ τ : UnitingSense) :
    UnitingUse → Bool → Bool → Prop
  | .uniterCauses => F.CausesBy σ
  | .noSelfCause => F.CausesBy τ

/-- An act frame over `Unit` with constant predicates. -/
abbrev af (formal virtual : Prop) : ActFrame Unit Unit :=
  ⟨fun _ _ => formal, fun _ _ => virtual, fun _ _ => True, fun _ _ => True,
    fun _ _ _ => True⟩

/-- The act uses read in two given senses. -/
abbrev ause {B : Type} (F : ActFrame B Unit) (σ τ : ActSense) : ActUse → B → Unit → Prop
  | .moverInAct => F.InActBy σ
  | .nonSimultaneity => F.InActBy τ

theorem not_ne_self (x : Bool) : (!x) ≠ x := by
  cases x
  · exact fun h => Bool.noConfusion h
  · exact fun h => Bool.noConfusion h

theorem controls : TermSenseForks2Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniting, exclusivity omitted: "uniter causes" read as uniting,
    -- "nothing causes itself" read as efficient; `true` unites itself
    refine ⟨fun x => x = true, fun _ x => x = true, uf true, fun _ => True,
      uuse (uf true) .uniting .efficient, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, Bool.noConfusion⟩
    · intro x a b ha _ _
      exact ⟨true, rfl, ha⟩
    · intro c a b x h
      exact h
    · intro u
      cases u with
      | uniterCauses => exact ⟨.uniting, trivial, rfl⟩
      | noSelfCause => exact ⟨.efficient, trivial, rfl⟩
    · intro h
      exact UnitingSense.noConfusion (h .uniting .efficient trivial trivial)
    · intro c a b x h
      exact ⟨a, b, h⟩
    · intro x h
      obtain ⟨_, hr⟩ := h
      exact hr
    · intro h
      obtain ⟨c, hne, hc⟩ := h true rfl
      exact hne hc.1
  · -- uniting, coverage omitted: the uses are `True` and `False`
    refine ⟨fun x => x = true, fun _ x => x = true, uf true, fun σ => σ = .efficient,
      fun u => match u with
        | .uniterCauses => fun _ _ => True
        | .noSelfCause => fun _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, Bool.noConfusion⟩
    · intro x a b ha _ _
      exact ⟨true, rfl, ha⟩
    · intro c a b x h
      exact h
    · intro h
      obtain ⟨σ, _, hσ⟩ := h .uniterCauses
      have hx := congrFun (congrFun hσ false) false
      cases σ with
      | efficient =>
        obtain ⟨_, hr⟩ := Eq.mp hx trivial
        exact hr
      | being => exact Bool.noConfusion (Eq.mp hx trivial).1
      | uniting =>
        obtain ⟨_, _, hu⟩ := Eq.mp hx trivial
        exact Bool.noConfusion hu.1
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · intro _ _ _ _ _
      trivial
    · intro _ h
      exact h
    · intro h
      obtain ⟨c, hne, hc⟩ := h true rfl
      exact hne hc.1
  · -- uniting, nonvacuity: `false` unites into `true` and causes its being
    refine ⟨fun x => x = true, fun _ x => x = true, uf false, fun σ => σ = .being,
      uuse (uf false) .being .being, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨false, true, hx, hx, Bool.noConfusion⟩
    · intro x a b ha _ _
      exact ⟨false, rfl, ha⟩
    · intro c a b x h
      exact h
    · intro u
      cases u with
      | uniterCauses => exact ⟨.being, rfl, rfl⟩
      | noSelfCause => exact ⟨.being, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · intro c a b x h
      exact h
    · intro x h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro x hx
      exact ⟨false, fun h => Bool.noConfusion (h.trans hx), rfl, hx⟩
    · exact ⟨true, rfl⟩
  · -- in act, exclusivity omitted: mover read virtually, non-simultaneity formally
    refine ⟨af False True, fun _ => True, ause (af False True) .virtually .formally,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      cases u with
      | moverInAct => exact ⟨.virtually, trivial, rfl⟩
      | nonSimultaneity => exact ⟨.formally, trivial, rfl⟩
    · intro h
      exact ActSense.noConfusion (h .virtually .formally trivial trivial)
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ _ => trivial
    · exact fun _ _ h => h.1
    · intro h
      exact h () () trivial trivial
  · -- in act, coverage omitted
    refine ⟨af False False, fun σ => σ = .formally,
      fun u => match u with
        | .moverInAct => fun _ _ => True
        | .nonSimultaneity => fun _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨σ, _, hσ⟩ := h .moverInAct
      have hx := congrFun (congrFun hσ ()) ()
      cases σ with
      | formally => exact Eq.mp hx trivial
      | virtually => exact Eq.mp hx trivial
      | formallyOrVirtually =>
        cases Eq.mp hx trivial with
        | inl h => exact h
        | inr h => exact h
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ _ => trivial
    · exact fun _ _ h => h.1
    · intro h
      exact h () () trivial trivial
  · -- in act, mixed reading
    refine ⟨af False True, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ _ => Or.inr trivial
    · exact fun _ _ h => h.1
    · intro h
      exact h () () trivial trivial
  · -- in act, nonvacuity over `Bool`: `true`, formally in act, moves `false`
    refine ⟨⟨fun x _ => x = true, fun _ _ => False, fun x _ => x = false,
        fun x _ => x = false, fun y x _ => y = true ∧ x = false⟩,
      fun σ => σ = .formally, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun u => match u with
        | .moverInAct => fun x _ => x = true
        | .nonSimultaneity => fun x _ => x = true
    · intro u
      cases u with
      | moverInAct => exact ⟨.formally, rfl, rfl⟩
      | nonSimultaneity => exact ⟨.formally, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · exact fun _ _ h => h
    · exact fun _ _ _ h => h.1
    · intro x _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · intro x _ _ h
      exact Bool.noConfusion (h.1.symm.trans h.2)
    · exact ⟨true, false, (), rfl, rfl⟩
  · -- becoming/being: another cause of coming to be, no cause of being
    refine ⟨⟨⟨fun _ _ => True, fun _ _ _ => False, id, fun x => !x, fun _ => False, ()⟩,
        fun c x => c ≠ x, fun _ => True⟩, ?_, ⟨true, trivial⟩, ?_⟩
    · intro x _
      exact ⟨!x, not_ne_self x, not_ne_self x⟩
    · intro h
      obtain ⟨_, _, hc⟩ := h true trivial
      exact hc
  · -- becoming/being: nonvacuity of the sense-2 route
    refine ⟨⟨⟨fun _ _ => True, fun c x _ => c ≠ x, id, fun x => !x, fun _ => False, ()⟩,
        fun _ _ => False, fun _ => True⟩, ?_, ?_, ⟨true, trivial⟩⟩
    · intro x _
      exact ⟨trivial, not_ne_self x⟩
    · intro x _
      exact ⟨!x, not_ne_self x, trivial, not_ne_self x⟩

end TruthCore.Results.Causality.TermSenseForks2
