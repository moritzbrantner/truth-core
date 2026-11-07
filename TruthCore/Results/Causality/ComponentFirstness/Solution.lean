module

public import TruthCore.Causality.ComponentFirstness

@[expose] public section

namespace TruthCore.Results.Causality.ComponentFirstness
open TruthCore.Causality.ComponentFirstness
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A component is in potency or participated. If in potency, act priority gives
something in act prior to it, firstness makes that thing the component itself,
and it would be in act and in potency in one respect. If participated, it has a
distinct cause of its being, which is prior to it, against firstness.
Conditional on five OPEN premises. -/
theorem noComponentFirst {B R : Type} (ComponentOf PriorSimply : B → B → Prop)
    (InAct InPotency : B → R → Prop) (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hKinds : ComponentIsPotentialOrParticipated ComponentOf InPotency Participated)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hParticipated : ParticipatedHasOtherCause Participated CausesIn esse)
    (hEfficient : EfficientCauseIsPriorToEffectReading CausesIn PriorSimply) :
    NoComponentIsFirstBeingReading ComponentOf PriorSimply := by
  intro p x hComponent hFirst
  rcases hKinds p x hComponent with ⟨r, hPotency⟩ | hPart
  · obtain ⟨y, hAct, hPrior⟩ := hActPrior p r hPotency
    have hEq : y = p := hFirst y hPrior
    subst hEq
    exact hNotBoth y r ⟨hAct, hPotency⟩
  · obtain ⟨c, hDistinct, hCause⟩ := hParticipated p hPart
    exact hDistinct (hFirst c (hEfficient c p esse hCause))

section Controls
open TruthCore.Causality.ComponentFirstness.Control

/-- With no priority, `false` (a component of `true`) is first. -/
theorem falseFirstNone : ¬ NoComponentIsFirstBeingReading comp none2 :=
  fun h => h false true ⟨rfl, rfl⟩ (fun _ hp => hp.elim)

theorem controls : Certificate :=
  ⟨⟨fun h => (h false true ⟨rfl, rfl⟩).elim (fun ⟨_, h⟩ => h) (fun h => h),
      fun _ _ h => h.elim, fun _ _ h => h.1.elim, fun _ h => h.elim,
      fun _ _ _ h => h.elim, falseFirstNone⟩,
    ⟨fun p _ hc => Or.inl ⟨(), hc.1⟩,
      fun h => (h false () rfl).elim (fun _ ⟨hAct, _⟩ => hAct),
      fun _ _ h => h.1.elim, fun _ h => h.elim, fun _ _ _ h => h.elim, falseFirstNone⟩,
    ⟨fun p _ hc => Or.inl ⟨(), hc.1⟩, fun x _ _ => ⟨x, trivial, rfl⟩,
      fun h => h false () ⟨trivial, rfl⟩, fun _ h => h.elim, fun _ _ _ h => h.elim,
      fun h => h false true ⟨rfl, rfl⟩ (fun _ hp => hp)⟩,
    ⟨fun p _ hc => Or.inr hc.1, fun _ _ h => h.elim, fun _ _ h => h.1.elim,
      fun h => (h false rfl).elim (fun _ ⟨_, hc⟩ => hc),
      fun _ _ _ h => h.elim, falseFirstNone⟩,
    ⟨fun p _ hc => Or.inr hc.1, fun _ _ h => h.elim, fun _ _ h => h.1.elim,
      fun x hx => ⟨true, fun h => Bool.noConfusion (h.trans hx), rfl, hx⟩,
      fun h => h true false () ⟨rfl, rfl⟩, falseFirstNone⟩,
    ⟨⟨fun p _ hc => Or.inr hc.1, fun _ _ h => h.elim, fun _ _ h => h.1.elim,
        fun x hx => ⟨true, fun h => Bool.noConfusion (h.trans hx), rfl, hx⟩,
        fun _ _ _ h => h⟩,
      fun _ _ hc hFirst => Bool.noConfusion ((hFirst true ⟨rfl, hc.1⟩).trans hc.1),
      ⟨rfl, rfl⟩⟩⟩

end Controls

end TruthCore.Results.Causality.ComponentFirstness
