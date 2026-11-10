module

public import TruthCore.Causality.SpineRivalsStageOne

@[expose] public section

namespace TruthCore.Results.Causality.SpineRivalsStageOne
open TruthCore.Causality.SpineRivalsStageOne
open TruthCore.Causality.SpineRivalsStageOne.Control
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty ConcreteEmptyAt
  PossiblyContingentsAbsentThenPresent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- In both three-world histories no moment of `near` or `far` is concrete-empty,
and every moment of `actual` is. -/
theorem awayInert (s t : Nat) (v : Place)
    (hEmpty : ∀ x : Bool, True → ¬ presentAway v x s) :
    ∀ x : Bool, True → ¬ presentAway v x t := by
  intro x _ hx
  cases v with
  | actual =>
    rcases hx with hx | hx
    · exact hx.2 rfl
    · exact Place.noConfusion hx.2.1
  | near => exact hEmpty false trivial (Or.inl ⟨rfl, fun e => Place.noConfusion e⟩)
  | far => exact hEmpty false trivial (Or.inl ⟨rfl, fun e => Place.noConfusion e⟩)

/-- Presence implies existence in the three-world assignment. -/
theorem awayPresence (v : Place) (x : Bool) (t : Nat) (hp : presentAway v x t) :
    existsAway v x := by
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr ⟨hp.1, hp.2.1⟩

/-- Rivals of the five stage-one premises survive with the remaining premises. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨⟨fun h => h rfl, fun _ => ⟨Place.near, fun e => Place.noConfusion e⟩⟩,
      fun _ _ _ _ hb => hb, awayPresence, fun v s t _ h => awayInert s t v h, ?_, ?_⟩,
    ⟨⟨fun _ => Or.inl rfl, Place.actual, Place.near, Place.actual,
        Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl rfl, ?_⟩,
      Or.inl rfl, awayPresence, fun v s t _ h => awayInert s t v h, ?_, ?_⟩,
    ⟨⟨fun _ _ => ⟨fun h => ⟨h.1, Or.inr ⟨h.2, by decide⟩⟩, fun h => ⟨h.1, ?_⟩⟩,
        true, false, 0, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩,
      fun _ _ _ _ _ => trivial, trivial, ?_, ?_, ?_⟩,
    ⟨⟨⟨false, trivial, rfl, true, trivial, fun e => Bool.noConfusion e⟩, fun _ _ h => h⟩,
      fun _ _ _ _ _ => trivial, trivial, ?_, ?_⟩,
    ⟨⟨bruteOnlyPossibleBeginning, bruteOnlyNoExternalCause⟩,
      fun _ _ _ _ _ => trivial, trivial, bruteOnlyNoNecessary⟩⟩
  -- group 1: possible contingent-free past, and no necessary individual at `actual`
  · refine ⟨Place.near, fun e => Place.noConfusion e, 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨Or.inr ⟨rfl, rfl⟩, Place.far, fun e => Place.noConfusion e, ?_⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · intro x _ hCont hx
      rcases hx with hx | hx
      · obtain ⟨_, u, hu, hAbsent⟩ := hCont
        exact hAbsent (Or.inl ⟨hx.1, hu⟩)
      · exact absurd hx.2.2 (by decide)
    · intro h
      rcases h with h | h
      · exact Bool.noConfusion h.1
      · exact Place.noConfusion h.2
  · rintro ⟨x, _, hEx, _⟩
    rcases hEx with h | h
    · exact h.2 rfl
    · exact Place.noConfusion h.2
  -- group 2
  · intro h
    rcases h with h | h | h
    · exact Place.noConfusion h
    · exact Place.noConfusion h.1
    · exact Place.noConfusion h.2
  · refine ⟨Place.near, Or.inr (Or.inl ⟨rfl, rfl⟩), 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨Or.inr ⟨rfl, rfl⟩, Place.far, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · intro x _ hCont hx
      rcases hx with hx | hx
      · obtain ⟨_, u, hu, hAbsent⟩ := hCont
        rcases hu with hu | hu | hu
        · subst hu; exact hAbsent (Or.inl ⟨hx.1, fun e => Place.noConfusion e⟩)
        · exact Place.noConfusion hu.1
        · obtain ⟨_, hu⟩ := hu
          subst hu; exact hAbsent (Or.inl ⟨hx.1, fun e => Place.noConfusion e⟩)
      · exact absurd hx.2.2 (by decide)
    · intro h
      rcases h with h | h
      · exact Bool.noConfusion h.1
      · exact Place.noConfusion h.2
  · rintro ⟨x, _, hEx, _⟩
    rcases hEx with h | h
    · exact h.2 rfl
    · exact Place.noConfusion h.2
  -- group 3
  · rcases h.2 with h' | h'
    · exact absurd h'.2 (by decide)
    · exact h'.1
  · intro h
    rcases h.2 with h' | h'
    · exact absurd h'.2 (by decide)
    · exact Bool.noConfusion h'.1
  · intro v s t hst hEmpty x _ hx
    have hs : s = 0 ∨ s ≠ 0 := Nat.eq_zero_or_pos s |>.imp id (fun h => Nat.ne_of_gt h)
    rcases hs with hs | hs
    · exact hEmpty false trivial ⟨hx.1, Or.inl ⟨rfl, hs⟩⟩
    · exact hEmpty true trivial ⟨hx.1, Or.inr ⟨rfl, hs⟩⟩
  · refine ⟨true, trivial, 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨⟨rfl, rfl⟩, false, trivial, fun e => Bool.false_ne_true e.1⟩, rfl, Or.inr ⟨rfl, by decide⟩⟩
    intro x _ hCont hx
    rcases hx.2 with h' | h'
    · exact Bool.false_ne_true (h'.1 ▸ hCont.1.2)
    · exact h'.2 rfl
  · rintro ⟨x, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial).1
  -- group 4
  · intro h
    obtain ⟨v, _, hBegins, _⟩ := h
    exact hBegins.elim
  · rintro ⟨c, _, he, hn⟩
    cases c with
    | false => exact Bool.noConfusion (hn true trivial)
    | true => exact Bool.false_ne_true he

end TruthCore.Results.Causality.SpineRivalsStageOne
