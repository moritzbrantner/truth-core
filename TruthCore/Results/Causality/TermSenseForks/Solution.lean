module

public import TruthCore.Causality.TermSenseForks

/-! Sense forks for "prior" and "cause": joint theorems by cases over the sense
enums, per-branch results, uses-agree from exclusivity, and controls.
Analyst formulations, attribution deferred. -/

@[expose] public section

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
  obtain ⟨σ, _, hσ⟩ := hCover ()
  have hEq : RoutePrior = F.PriorIn σ := hσ
  subst hEq
  cases σ with
  | simply =>
    intro x r hPot
    obtain ⟨y, hAct, hPrior⟩ := hRoute x r hPot
    exact ⟨y, hAct, hPrior⟩
  | inTime =>
    exfalso
    obtain ⟨n, r, hNone, hPot⟩ := hFirst
    obtain ⟨y, _, hPrior⟩ := hRoute n r hPot
    exact hNone y hPrior
  | inSubstance =>
    intro x r hPot
    obtain ⟨y, hAct, hPrior⟩ := hRoute x r hPot
    exact ⟨y, hAct, hBridge y x hPrior⟩

/-- The temporal branch is refuted: if some temporally first being is in
potency, act is not prior to potency in time. -/
theorem actNotPriorInTime {Being Respect : Type} (F : PriorityFrame Being Respect)
    (hFirst : TemporallyFirstBeingInPotency F) : ActNotPriorInTime F := by
  intro hTime
  obtain ⟨n, r, hNone, hPot⟩ := hFirst
  obtain ⟨y, _, hPrior⟩ := hTime n r hPot
  exact hNone y hPrior

/-- The substance branch: act's priority in substance over every potency, with
the open bridge to simple priority, gives act's simple priority. -/
theorem actSimplyPriorFromSubstance {Being Respect : Type}
    (F : PriorityFrame Being Respect)
    (hSubst : ActPriorInSubstance F)
    (hBridge : PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply) :
    ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply := by
  intro x r hPot
  obtain ⟨y, hAct, hPrior⟩ := hSubst x r hPot
  exact ⟨y, hAct, hBridge y x hPrior⟩

/-- Coverage and exclusivity block equivocation: every use of "prior" on the
route stands for one relation. -/
theorem priorRouteUsesAgree {Being Respect : Type} {U : Type}
    (F : PriorityFrame Being Respect) (Select : PrioritySense → Prop)
    (use : U → Being → Being → Prop)
    (hCover : PriorSensesExhaustive F Select use)
    (hUnique : PriorSenseUnique Select) :
    PriorRouteUsesAgree use :=
  usesAgree_of_cover_unique F.PriorIn Select use hCover hUnique

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
  obtain ⟨σ, _, hσ⟩ := hCover ()
  have hEq : RouteCause = F.CausesBy σ := hσ
  subst hEq
  cases σ with
  | moving =>
    intro x r h
    exact hRoute x r (hMove x r h)
  | efficient =>
    intro x r h
    exact hRoute x r h
  | perfection =>
    exfalso
    obtain ⟨x, r, h⟩ := hPerf
    exact hRoute x r h
  | origin =>
    intro x r h
    have hO : F.CausesOrigin x x := hOrigin x r h
    exact hRoute x r hO

/-- The perfection branch is refuted: a self-perfecting subject falsifies
"nothing causes a perfection in itself". -/
theorem ownPerfectionNotAlwaysExternal {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hPerf : SomeSubjectCausesItsOwnPerfection F) :
    OwnPerfectionNotAlwaysExternal F := by
  intro hNone
  obtain ⟨x, r, h⟩ := hPerf
  exact hNone x r h

/-- The moving branch: Aristotle's reading that no mover moves itself, with
the open bridge, gives that nothing is its own efficient cause. -/
theorem noSelfEfficientCauseFromNoSelfMover {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hNoSelf : TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
      F.MovesIn)
    (hMove : SelfEfficientCausationIsSelfMoving F) :
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn :=
  fun x r h => hNoSelf x x r (hMove x r h) rfl

/-- The origin branch: no self-origination, with the open bridge, gives that
nothing is its own efficient cause. -/
theorem noSelfEfficientCauseFromOrigin {Being Respect : Type}
    (F : CauseFrame Being Respect)
    (hNoOrigin : NothingOriginatesItself F)
    (hOrigin : SelfEfficientCausationIsSelfOrigination F) :
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn :=
  fun x r h => hNoOrigin x (hOrigin x r h)

/-- Strength order: Aristotle's unrestricted reading (no mover moves itself in
any respect) implies the prima via's same-respect reading. -/
theorem noSelfMovingSameRespectFromNoSelfMover {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hAny : TruthCore.Greek.Aristotle.Physics.Typed.NoMoverMovesItselfInItsRespectReading
      MovesIn) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn :=
  fun x r _ h => hAny x x r h rfl

/-- Coverage and exclusivity block equivocation on "cause". -/
theorem causeRouteUsesAgree {Being Respect : Type} {U : Type}
    (F : CauseFrame Being Respect) (Select : CauseSense → Prop)
    (use : U → Being → Being → Respect → Prop)
    (hCover : CauseSensesExhaustive F Select use)
    (hUnique : CauseSenseUnique Select) :
    CauseRouteUsesAgree use :=
  usesAgree_of_cover_unique F.CausesBy Select use hCover hUnique

/-! ## Controls -/

/-- A frame with the given relations over `Unit`. -/
abbrev pf (act pot simply time subst : Prop) : PriorityFrame Unit Unit :=
  ⟨fun _ _ => act, fun _ _ => pot, fun _ _ => simply, fun _ _ => time, fun _ _ => subst⟩

theorem priorForkControls : PriorForkControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- coverage fails: the route relation is `True`, every sense relation `False`
    refine ⟨pf True True False False False, fun _ => True, fun _ _ => True,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨σ, _, hσ⟩ := h ()
      have hx := congrFun (congrFun hσ ()) ()
      cases σ <;> exact Eq.mp hx trivial
    · exact fun _ _ _ => ⟨(), trivial, trivial⟩
    · exact fun _ _ h => h
    · exact ⟨(), (), fun _ h => h, trivial⟩
    · intro h
      obtain ⟨_, _, hP⟩ := h () () trivial
      exact hP
  · -- the route premise fails
    refine ⟨pf True True False False False, fun σ => σ = .simply, fun _ _ => False,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.simply, rfl, rfl⟩
    · intro h
      obtain ⟨_, _, hP⟩ := h () () trivial
      exact hP
    · exact fun _ _ h => h
    · exact ⟨(), (), fun _ h => h, trivial⟩
    · intro h
      obtain ⟨_, _, hP⟩ := h () () trivial
      exact hP
  · -- the substance bridge fails; the route reads "prior" in substance
    refine ⟨pf True True False False True, fun σ => σ = .inSubstance, fun _ _ => True,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.inSubstance, rfl, rfl⟩
    · exact fun _ _ _ => ⟨(), trivial, trivial⟩
    · intro h
      exact h () () trivial
    · exact ⟨(), (), fun _ h => h, trivial⟩
    · intro h
      obtain ⟨_, _, hP⟩ := h () () trivial
      exact hP
  · -- no temporally first being in potency; the route reads "prior" in time
    refine ⟨pf True True False True False, fun σ => σ = .inTime, fun _ _ => True,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.inTime, rfl, rfl⟩
    · exact fun _ _ _ => ⟨(), trivial, trivial⟩
    · exact fun _ _ h => h
    · intro h
      obtain ⟨_, _, hNone, _⟩ := h
      exact hNone () trivial
    · intro h
      obtain ⟨_, _, hP⟩ := h () () trivial
      exact hP
  · -- nonvacuity
    refine ⟨pf True True True False False, fun σ => σ = .simply, fun _ _ => True,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.simply, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · exact fun _ _ _ => ⟨(), trivial, trivial⟩
    · exact fun _ _ _ => trivial
    · exact ⟨(), (), fun _ h => h, trivial⟩
    · exact fun _ _ _ => ⟨(), trivial, trivial⟩
    · exact ⟨(), (), trivial⟩
    · exact ⟨(), (), trivial⟩
  · -- two senses selected: uses disagree
    refine ⟨pf True True True False False, fun _ => True,
      fun b => if b then (fun _ _ => True) else (fun _ _ => False), ?_, ?_, ?_⟩
    · intro b
      cases b with
      | true => exact ⟨.simply, trivial, rfl⟩
      | false => exact ⟨.inTime, trivial, rfl⟩
    · intro h
      exact PrioritySense.noConfusion (h .simply .inTime trivial trivial)
    · intro h
      have hx := congrFun (congrFun (h true false) ()) ()
      exact Eq.mp hx trivial

/-- A causal frame with the given relations over `Unit`. -/
abbrev cf (moved moves eff perf orig : Prop) : CauseFrame Unit Unit :=
  ⟨fun _ _ => moved, fun _ _ _ => moves, fun _ _ _ => eff, fun _ _ _ => perf,
    fun _ _ => orig⟩

theorem causeForkControls : CauseForkControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- coverage fails: the route relation is `False`, every sense relation `True`
    refine ⟨cf True True True True True, fun _ => True, fun _ _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨σ, _, hσ⟩ := h ()
      have hx := congrFun (congrFun (congrFun hσ ()) ()) ()
      cases σ <;> exact Eq.mpr hx trivial
    · exact fun _ _ h => h
    · exact ⟨(), (), trivial⟩
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ => trivial
    · intro h
      exact h () () trivial
  · -- the route premise fails; efficient reading
    refine ⟨cf True True True True True, fun σ => σ = .efficient, fun _ _ _ => True,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.efficient, rfl, rfl⟩
    · intro h
      exact h () () trivial
    · exact ⟨(), (), trivial⟩
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ => trivial
    · intro h
      exact h () () trivial
  · -- no self-perfecting subject; perfection reading
    refine ⟨cf True True True False True, fun σ => σ = .perfection, fun _ _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.perfection, rfl, rfl⟩
    · exact fun _ _ h => h
    · intro h
      obtain ⟨_, _, hP⟩ := h
      exact hP
    · exact fun _ _ _ => trivial
    · exact fun _ _ _ => trivial
    · intro h
      exact h () () trivial
  · -- the moving bridge fails; moving reading
    refine ⟨cf True False True True True, fun σ => σ = .moving, fun _ _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.moving, rfl, rfl⟩
    · exact fun _ _ h => h
    · exact ⟨(), (), trivial⟩
    · intro h
      exact h () () trivial
    · exact fun _ _ _ => trivial
    · intro h
      exact h () () trivial
  · -- the origin bridge fails; origin reading
    refine ⟨cf True True True True False, fun σ => σ = .origin, fun _ _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.origin, rfl, rfl⟩
    · exact fun _ _ h => h
    · exact ⟨(), (), trivial⟩
    · exact fun _ _ _ => trivial
    · intro h
      exact h () () trivial
    · intro h
      exact h () () trivial
  · -- nonvacuity over `Bool`: `true` efficiently causes `false`
    refine ⟨⟨fun _ _ => True, fun _ _ _ => True, fun c x _ => c = true ∧ x = false,
        fun _ _ _ => True, fun _ _ => False⟩,
      fun σ => σ = .efficient, fun c x _ => c = true ∧ x = false,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨.efficient, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · intro x r h
      obtain ⟨h1, h2⟩ := h
      exact Bool.noConfusion (h1.symm.trans h2)
    · exact ⟨true, (), trivial⟩
    · exact fun _ _ _ => trivial
    · intro x r h
      obtain ⟨h1, h2⟩ := h
      exact Bool.noConfusion (h1.symm.trans h2)
    · intro x r h
      obtain ⟨h1, h2⟩ := h
      exact Bool.noConfusion (h1.symm.trans h2)
    · exact ⟨true, false, (), rfl, rfl⟩
  · -- two senses selected: uses disagree
    refine ⟨cf True True False True True, fun _ => True,
      fun b => if b then (fun _ _ _ => True) else (fun _ _ _ => False), ?_, ?_, ?_⟩
    · intro b
      cases b with
      | true => exact ⟨.moving, trivial, rfl⟩
      | false => exact ⟨.efficient, trivial, rfl⟩
    · intro h
      exact CauseSense.noConfusion (h .moving .efficient trivial trivial)
    · intro h
      have hx := congrFun (congrFun (congrFun (h true false) ()) ()) ()
      exact Eq.mp hx trivial

/-- The batch controls. -/
theorem controls : TermSenseForkControls :=
  ⟨priorForkControls, causeForkControls⟩

end TruthCore.Results.Causality.TermSenseForks
