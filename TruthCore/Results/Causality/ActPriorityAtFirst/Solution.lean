module

public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Causality.ComponentFirstness
public import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

@[expose] public section

namespace TruthCore.Results.Causality.ActPriorityAtFirst
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Strength order: act's simple priority over every potency of the
independently supplied potency parameter (`IndependentPriority`, the transparent
wrapper of `ActSimplyPriorToPotencyReading`) gives it at first beings. An
instance, not a new derivation. -/
theorem weakOfStrong {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop)
    (hStrong : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      InAct InPotency PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply :=
  fun f _ r hPot => hStrong f r hPot

/-- `noComponentFirst` with act priority only at first beings: a component in
potency, if first, would by the weak version have a prior being in act in that
respect, which firstness makes the component itself, against non-overlap; a
participated component has a distinct cause of its being, which is prior to it.
Conditional on five OPEN premises. -/
theorem noComponentFirstOfWeak {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hWeak : FirstBeingActPriority InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherCause Participated CausesIn esse)
    (hEfficient : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  intro p x hComponent hFirst
  rcases hKinds p x hComponent with ⟨r, hPotency⟩ | hPart
  · obtain ⟨y, hAct, hPrior⟩ := hWeak p hFirst r hPotency
    have hEq : y = p := hFirst y hPrior
    subst hEq
    exact hNotBoth y r ⟨hAct, hPotency⟩
  · obtain ⟨c, hDistinct, hCause⟩ := hParticipated p hPart
    exact hDistinct (hFirst c (hEfficient c p esse hCause))

/-- The weak version from composition: a first being is in act in some respect,
so if it were in potency in another it would be composite, and so it would have
a distinct cause of its being, which would be prior to it, against firstness.
Conditional on four OPEN premises. -/
theorem weakOfComposition {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) (Composite : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hInAct : FirstBeingIsInSomeAct InAct PriorSimply)
    (hComposite : ActAndPotencyMakeComposite InAct InPotency Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hEfficient : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  intro f hFirst r hPot
  obtain ⟨s, hAct⟩ := hInAct f hFirst
  obtain ⟨c, hDistinct, hCauses⟩ := hCause f (hComposite f r s hAct hPot)
  exact absurd (hFirst c (hEfficient c f esse hCauses)) hDistinct

section Controls
open TruthCore.Causality.ActPriorityAtFirst.Control

theorem coldStone : ColdStone := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩, ?_⟩
  · intro f hFirst r hPot
    cases f
    · exact Bool.noConfusion (hFirst true ⟨rfl, rfl⟩)
    · exact Bool.noConfusion hPot.1
  · intro _ _ h
    rcases h with ⟨hAct, _, hr⟩
    rw [hr] at hAct
    exact Bool.noConfusion hAct
  · intro f _; exact ⟨true, rfl⟩
  · intro _ _ _ _ h; exact h.1
  · intro x hx; exact ⟨true, by rw [hx]; exact Bool.noConfusion, rfl, hx⟩
  · intro _ _ _ h; exact h
  · intro y hy; exact Bool.noConfusion hy.2
  · intro h
    obtain ⟨_, hAct, _⟩ := h false false ⟨rfl, rfl⟩
    exact Bool.noConfusion hAct

/-- The stone, first under no priority and in potency to heat, falsifies the
weak version when nothing is in act in heat. -/
private theorem weakFails (InAct : Bool → Bool → Prop) (hHeat : ∀ y, ¬ InAct y false) :
    ¬ FirstBeingActPriority InAct stonePotency noPrior := by
  intro h
  obtain ⟨y, hAct, _⟩ := h false (fun _ h => h.elim) false ⟨rfl, rfl⟩
  exact hHeat y hAct

private theorem esseNoHeat : ∀ y, ¬ esseAct y false := fun _ h => Bool.noConfusion h

private theorem esseNotBoth : NotActAndPotencyInSameRespectReading esseAct stonePotency := by
  intro _ _ h
  rcases h with ⟨hAct, _, hr⟩
  rw [hr] at hAct
  exact Bool.noConfusion hAct

theorem compositionOmissions : CompositionOmissions := by
  have hInAct : FirstBeingIsInSomeAct esseAct noPrior := fun _ _ => ⟨true, rfl⟩
  refine ⟨⟨fun _ _ _ h => h.elim, fun _ h => h.elim, fun _ _ _ h => h.elim,
      fun _ _ h => h.1.elim, ?_, weakFails noAct (fun _ h => h)⟩,
    ⟨hInAct, fun _ h => h.elim, fun _ _ _ h => h.elim, esseNotBoth, ?_,
      weakFails esseAct esseNoHeat⟩,
    ⟨hInAct, fun _ _ _ _ h => h.1, fun _ _ _ h => h.elim, esseNotBoth, ?_,
      weakFails esseAct esseNoHeat⟩,
    ⟨hInAct, fun _ _ _ _ h => h.1, fun x hx => ⟨true, by rw [hx]; exact Bool.noConfusion, rfl, hx⟩,
      esseNotBoth, ?_, weakFails esseAct esseNoHeat⟩⟩
  · intro h
    obtain ⟨_, hAct⟩ := h true (fun _ h => h.elim)
    exact hAct
  · intro h; exact h false false true rfl ⟨rfl, rfl⟩
  · intro h
    obtain ⟨_, _, hc⟩ := h false rfl
    exact hc
  · intro h; exact h true false true ⟨rfl, rfl⟩

theorem facts : Facts := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B R InAct InPotency PriorSimply h
    exact fun f _ r hPot => h f r hPot
  · intro B R InAct InPotency PriorSimply hWeak hNotBoth f hFirst r hPot
    obtain ⟨y, hAct, hPrior⟩ := hWeak f hFirst r hPot
    have hEq : y = f := hFirst y hPrior
    subst hEq
    exact hNotBoth y r ⟨hAct, hPot⟩
  · intro B R InAct InPotency PriorSimply hNo f hFirst r hPot
    exact absurd hPot (hNo f hFirst r)
  · intro B R InAct InPotency PriorSimply G hStrong hNotBoth hBridge x r hPot
    obtain ⟨y, hAct, hPrior⟩ := hStrong x r hPot
    have hNe : y ≠ x := by
      intro hEq
      subst hEq
      exact hNotBoth y r ⟨hAct, hPot⟩
    exact ⟨y, hNe, hAct, hBridge y x hNe hPrior⟩
  · refine ⟨fun f _ r _ => ⟨f, trivial, trivial⟩, ?_⟩
    intro h
    exact h () (fun _ _ => rfl) () trivial

/-- All controls and facts of the batch. -/
theorem controls : Certificate := ⟨coldStone, compositionOmissions, facts⟩

end Controls

end TruthCore.Results.Causality.ActPriorityAtFirst
