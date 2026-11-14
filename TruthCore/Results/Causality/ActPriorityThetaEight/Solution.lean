module

public import TruthCore.Causality.ActPriorityThetaEight
public import TruthCore.Results.Causality.ActPriorityAtFirst.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ActPriorityThetaEight
open TruthCore.Causality.ActPriorityThetaEight
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionCausingInAnotherIsEfficient)

/-- Θ.8, the eternal: a first being is in act in some respect, namely in being,
because it cannot fail to be (OPEN) and whatever is simply incorruptible is in
act in substance (*In Metaph.* IX lect. 9 n. 5-6 reading). -/
theorem inActOfIncorruptible {B R : Type} (InAct CanFailToBe : B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse) :
    FirstBeingIsInSomeAct InAct PriorSimply :=
  fun f hFirst => ⟨esse, hInAct f (hIncorruptible f hFirst)⟩

/-- Strength order: the composition premise gives its instance at act in
being. -/
theorem restrictedOfComposition {B R : Type} (InAct InPotency : B → R → Prop) (esse : R)
    (Composite : B → Prop)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite) :
    ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite :=
  fun x r hAct hPot => hComposite x r esse hAct hPot

/-- Θ.8, the eternal, with composition: a first being cannot fail to be, so it
is in act in being; if it were in potency in some respect it would be
composite, so it would have a distinct cause of its being, which by the bridge
causes it efficiently and so is prior to it, against firstness. Composes
`firstBeingNoPotencyOfComposition` at act read as act in being. Conditional on
six OPEN premises. -/
theorem firstBeingNoPotencyOfThetaEight {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply :=
  TruthCore.Results.Causality.ActPriorityAtFirst.firstBeingNoPotencyOfComposition
    (fun x _ => InAct x esse) InPotency PriorSimply Composite CausesIn EfficientlyCausesIn
    esse (fun f hFirst => ⟨esse, hInAct f (hIncorruptible f hFirst)⟩)
    (fun x r _ hAct hPot => hComposite x r hAct hPot) hCause hBridge hEfficient

/-- Plenitude plus change-cause: a first being in potency in a respect now can
be in act in it (definitional priority read as an open bridge); by plenitude
over an infinite past it was in act in it at some earlier time; so it has an
efficient cause other than itself, which is prior to it, against firstness.
Concludes no potency at `now` only. Uses no composition premise and no cause of
composites. Conditional on five OPEN premises. -/
theorem firstBeingNoPotencyOfPlenitude {B R T : Type}
    (InActAt InPotencyAt : T → B → R → Prop) (PriorSimply : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) (Before : T → T → Prop) (now : T)
    (Possible : (T → Prop) → Prop)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hPast : PastIsInfinite Before now)
    (hPossible : PotencyMakesActPossible InActAt InPotencyAt Possible)
    (hChange : ActThenPotencyHasAnotherCause Before InActAt InPotencyAt EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingIsInNoWayInPotencyAt InPotencyAt PriorSimply now := by
  intro f hFirst r hPot
  obtain ⟨t', hBefore, hAct⟩ := hPlenitude hPast _ (hPossible now f r hPot)
  obtain ⟨c, s, hDistinct, hCauses⟩ := hChange t' now f r hBefore hAct hPot
  exact hDistinct (hFirst c (hEfficient c f s hCauses))

/-- The weak version from the Θ.8 route: by `firstBeingNoPotencyOfThetaEight`
a first being is in potency in no respect, so first-being act priority holds
vacuously. Same six OPEN premises, all with the independent POTENCY_2
parameter. -/
theorem weakOfThetaEight {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn EfficientlyCausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBridge : PerfectionCausingInAnotherIsEfficient CausesIn EfficientlyCausesIn)
    (hEfficient : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  intro f hFirst r hPot
  exact absurd hPot (firstBeingNoPotencyOfThetaEight InAct InPotency CanFailToBe PriorSimply
    Composite CausesIn EfficientlyCausesIn esse hIncorruptible hInAct hComposite hCause hBridge
    hEfficient f hFirst r)

section Controls
open TruthCore.Causality.ActPriorityThetaEight.Control

private theorem noPriorFirst (f : Bool) : IsFirstBeing noPrior f := fun _ h => h.elim

theorem heavenlyFirst : HeavenlyFirst := by
  refine ⟨fun _ _ h => h, ?_, ?_, fun _ _ => ⟨true, rfl⟩, ?_, noPriorFirst false, rfl, ?_⟩
  · intro _ _; rfl
  · intro _ _ h; exact Bool.noConfusion h
  · intro _ _ h
    rcases h with ⟨hAct, hPot⟩
    unfold esseAct at hAct; unfold placePotency at hPot
    rw [hAct] at hPot; exact Bool.noConfusion hPot
  · intro h
    obtain ⟨y, hAct, _⟩ := h false (noPriorFirst false) false rfl
    exact Bool.noConfusion hAct

theorem contingentFirst : ContingentFirst :=
  ⟨fun _ _ => ⟨true, rfl⟩, fun h => h false (noPriorFirst false) trivial⟩

theorem restrictedStrict : RestrictedStrict := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ hAct _; exact Bool.noConfusion hAct
  · intro h; exact h false true false rfl rfl
  · intro h; exact Bool.noConfusion (h false false rfl)

theorem idleUncausedComposite : IdleUncausedComposite := by
  refine ⟨fun _ _ => ⟨true, rfl⟩, ?_, fun _ _ => rfl, fun _ _ h => h, fun _ _ _ _ _ => trivial,
    fun _ _ _ _ => trivial, fun _ _ _ _ h => h, fun _ _ _ h => h.elim, ?_,
    fun _ _ _ _ => trivial, ?_, ?_, ?_, ?_, noPriorFirst false, trivial, ?_, ?_⟩
  · intro _ _ h; exact Bool.noConfusion h
  · intro t _; exact ⟨t - 1, by omega⟩
  · intro _ _ _ _ _ hAct hPot
    unfold esseActAt at hAct; unfold placePotencyAt at hPot
    rw [hAct] at hPot; exact Bool.noConfusion hPot
  · intro _ _ h
    rcases h with ⟨hAct, hPot⟩
    unfold esseActAt at hAct; unfold placePotencyAt at hPot
    rw [hAct] at hPot; exact Bool.noConfusion hPot
  · intro h
    obtain ⟨_, _, hc⟩ := h false trivial
    exact hc
  · intro h
    obtain ⟨_, _, hAct⟩ := h (fun t _ => ⟨t - 1, by omega⟩)
      (fun t => esseActAt t false false) trivial
    exact Bool.noConfusion hAct
  · intro t; exact ⟨rfl, fun h => Bool.noConfusion h⟩
  · intro h; exact h false (noPriorFirst false) false rfl

theorem thetaEightOmissions : ThetaEightOmissions := by
  delta ThetaEightOmissions FirstBeingIsIncorruptibleSimply IsFirstBeing IncorruptibleSimply
    IncorruptibleIsInActReading ActInBeingAndPotencyMakeComposite
    CompositeHasAUnitingCauseReading PerfectionCausingInAnotherIsEfficient
    EfficientCauseIsPriorToEffectReading FirstBeingIsInNoWayInPotencyReading PureAct
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem intPast : PastIsInfinite (· < ·) (0 : Int) :=
  fun t _ => ⟨t - 1, by omega⟩

private theorem unitPotentFirst :
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => False) :=
  fun h => h () (fun _ h => h.elim) () trivial

private theorem realizedPlenitude :
    PlenitudeOverInfinitePastReading (· < ·) (0 : Int) realizedBefore :=
  fun _ _ h => h

theorem plenitudeOmissions : PlenitudeOmissions := by
  refine ⟨⟨?_, intPast, fun _ _ _ _ => trivial, fun _ _ _ _ _ h => h.elim,
      fun _ _ _ h => h.elim, unitPotentFirst⟩,
    ⟨?_, ?_, fun _ _ _ _ => trivial, fun _ _ _ _ _ h => h.elim,
      fun _ _ _ h => h.elim, unitPotentFirst⟩,
    ⟨fun _ _ h => h.elim, intPast, ?_, fun _ _ _ _ _ h => h.elim,
      fun _ _ _ h => h.elim, unitPotentFirst⟩,
    ⟨realizedPlenitude, intPast, ?_, ?_, fun _ _ _ h => h.elim, ?_⟩,
    ⟨realizedPlenitude, intPast, ?_, ?_, ?_, ?_⟩,
    ⟨realizedPlenitude, intPast, ?_, ?_, ?_, ?_, ⟨rfl, by decide⟩, ?_⟩⟩
  -- (1) plenitude fails
  · intro h
    obtain ⟨_, _, hφ⟩ := h intPast (fun _ => False) trivial
    exact hφ
  -- (2) Nat: plenitude vacuous, past finite
  · intro hPast
    obtain ⟨_, h⟩ := hPast 0 (Or.inl rfl)
    exact absurd h (Nat.not_lt_zero _)
  · intro h
    obtain ⟨_, h⟩ := h 0 (Or.inl rfl)
    exact Nat.not_lt_zero _ h
  -- (3) potency without possibility
  · intro h; exact h 0 () () trivial
  -- (4) lone being changes uncaused
  · intro t _ _ _; exact ⟨-1, by decide, by unfold actBeforeNow; decide⟩
  · intro h
    obtain ⟨c, _, hne, _⟩ := h (-1) 0 () () (by decide)
      (by unfold actBeforeNow; decide) (by unfold potencyFromNow; decide)
    exact hne rfl
  · intro h
    exact h () (fun _ h => h.elim) () (by unfold potencyFromNow; decide)
  -- (5) cause without priority
  · intro t x _ h; exact ⟨-1, by decide, h.1, by decide⟩
  · intro _ _ x _ _ hAct _
    exact ⟨true, (), by rw [hAct.1]; decide, rfl, hAct.1⟩
  · intro h; exact h true false () ⟨rfl, rfl⟩
  · intro h
    exact h false (fun _ h => h.elim) () ⟨rfl, by decide⟩
  -- (6) witness
  · intro t x _ h; exact ⟨-1, by decide, h.1, by decide⟩
  · intro _ _ x _ _ hAct _
    exact ⟨true, (), by rw [hAct.1]; decide, rfl, hAct.1⟩
  · intro c x _ h; exact h
  · intro y h; exact absurd h.2 (by decide)
  · intro f hFirst _ hPot
    rcases hPot with ⟨hf, _⟩
    subst hf
    exact Bool.noConfusion (hFirst true ⟨rfl, rfl⟩)

theorem facts : Facts := by
  refine ⟨?_, ?_, ?_⟩
  · intro B R InAct InPotency esse Composite h x r hAct hPot
    exact h x r esse hAct hPot
  · intro B R InAct InPotency esse Composite hBeing h x r s hAct hPot
    exact h x r (hBeing x s hAct) hPot
  · intro B R InAct esse PriorSimply hBeing h f hFirst
    obtain ⟨s, hAct⟩ := h f hFirst
    exact hBeing f s hAct

/-- All controls and facts of the batch. -/
theorem controls : Certificate :=
  ⟨heavenlyFirst, contingentFirst, restrictedStrict, idleUncausedComposite,
    thetaEightOmissions, plenitudeOmissions, facts⟩

end Controls

end TruthCore.Results.Causality.ActPriorityThetaEight
