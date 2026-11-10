module

public import TruthCore.Causality.ContingentComingToBe
public import TruthCore.Results.Causality.InertEmptiness.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ContingentComingToBe
open TruthCore.Causality.ContingentComingToBe
open TruthCore.Causality.InertEmptiness (ContingentsAbsentThenPresentAt
  PossiblyContingentsAbsentThenPresent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Below or at a moment with a founded past there is a moment with nothing
strictly earlier. -/
theorem minimalBelow {T : Type} [Preorder T] (s : T)
    (hAcc : Acc (fun a b : T => a < b) s) :
    ∃ m, (m = s ∨ m < s) ∧ ∀ r, ¬ r < m := by
  induction hAcc with
  | intro s _ ih =>
    by_cases hLower : ∃ r, r < s
    · obtain ⟨r, hr⟩ := hLower
      obtain ⟨m, hm, hMin⟩ := ih r hr
      refine ⟨m, Or.inr ?_, hMin⟩
      rcases hm with rfl | hm
      · exact hr
      · exact lt_trans hm hr
    · exact ⟨s, Or.inl rfl, fun r hr => hLower ⟨r, hr⟩⟩

/-- In a history of founded coming-to-be there is a moment free of contingent
concrete individuals strictly before a moment containing one: the earliest
moment below the founded one. Anything contingent present there would need a
still earlier moment of absence. -/
theorem absentThenPresentAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W)
    (hFounded : FoundedComingToBeAt h Concrete v) :
    ContingentsAbsentThenPresentAt h Concrete v := by
  obtain ⟨hCome, x, t, hx, hCont, hxt, hAcc⟩ := hFounded
  obtain ⟨s, hst, _⟩ := hCome x hx hCont t hxt
  obtain ⟨m, hm, hMin⟩ := minimalBelow s (hAcc.inv hst)
  have hmt : m < t := by
    rcases hm with rfl | hm
    · exact hst
    · exact lt_trans hm hst
  refine ⟨m, t, hmt, ?_, x, hx, hCont, hxt⟩
  intro y hy hyCont hym
  obtain ⟨r, hr, _⟩ := hCome y hy hyCont m hym
  exact hMin r hr

/-- The possibility of founded coming-to-be gives the possible contingent-free
past (premise A3 of the modal spine). No frame condition, presence contract or
inertness of emptiness is used. -/
theorem possibleContingentFreePast {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hPossible : PossiblyFoundedComingToBe h Concrete w) :
    PossiblyContingentsAbsentThenPresent h Concrete w := by
  obtain ⟨v, hwv, hFounded⟩ := hPossible
  exact ⟨v, hwv, absentThenPresentAt h Concrete v hFounded⟩

/-- No integer time has a founded past. -/
theorem intNotAcc (t : Int) : ¬ Acc (fun a b : Int => a < b) t := by
  intro hAcc
  induction hAcc with
  | intro t _ ih => exact ih (t - 1) (by omega)

/-- Survival models of the initial-state rival and a witness of the new premise. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨fun v _ _ hp => hp.1, ?_, ?_, ?_, intNotAcc, ?_⟩,
    ⟨⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩, ?_⟩, ?_⟩
  · intro v s t hst hEmpty x _ hxt
    exact hEmpty s trivial ⟨hxt.1, le_refl s⟩
  · intro x _ _ t hxt
    exact ⟨x - 1, by have := hxt.2; omega, fun hp => by have := hp.2; omega⟩
  · rintro v _ ⟨s, t, _, hAbsent, x, _, _, hxt⟩
    exact hAbsent s trivial ⟨hxt.1, false, trivial, Bool.false_ne_true⟩ ⟨hxt.1, le_refl s⟩
  · rintro ⟨_, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial)
  · intro hCome
    obtain ⟨s, hs, _⟩ := hCome () trivial ⟨rfl, false, trivial, Bool.false_ne_true⟩ 0 rfl
    exact Nat.not_lt_zero s hs
  · refine ⟨true, trivial, ?_, true, 1, trivial,
      ⟨Or.inr rfl, false, trivial, TruthCore.Results.Causality.InertEmptiness.absentAtFalse⟩,
      Or.inr ⟨rfl, rfl⟩, Nat.lt_wfRel.wf.apply 1⟩
    intro x _ hCont t hxt
    rcases hxt with hx | hx
    · subst hx
      obtain ⟨_, u, _, hAbsent⟩ := hCont
      exact absurd (Or.inl rfl) hAbsent
    · exact ⟨0, by omega, fun hp => by
        rcases hp with hp | hp
        · subst hp
          obtain ⟨_, u, _, hAbsent⟩ := hCont
          exact hAbsent (Or.inl rfl)
        · exact absurd hp.2 (by decide)⟩

end TruthCore.Results.Causality.ContingentComingToBe
