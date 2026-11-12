module

public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.DeiFiliusUnifiedRoute
public import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion

/-! Two typed senses of "creature" and the passage between them

`DEF-CREATURE` (ST I q.13 a.5: creatures are ordered to God as to their
principle and cause) was carried in Lean by one uninterpreted predicate
`Creature`. Two premises of the corpus use it in different extensions: the open
premise `CausedInBeingByAnotherIsCreature` was glossed broadly (ordered to *some*
cause of its being, secondary causes included), while `CreatureEsseIsReceived`
generalizes ST I q.7 a.2, which speaks of things made by God. Chained through one
predicate they equivocate (the rejected first draft of #1494).

This module gives each sense its own Lean declaration:

* CREATURE_1, `IsCreatureOfUniversalCause`: x is caused as to its being by some
  being g other than x that causes the being of every other being in act
  (`CausesAllInGenus` at esse, the q.2 a.3 *causa esse omnibus entibus*). This
  is the narrow sense of `DEF-CREATURE`, with "God" read as a universal cause of
  being; the reading of God by that description is the Fourth Way's own (*et hoc
  dicimus Deum*), and uniqueness of the universal cause is not built in.
* CREATURE_2, `IsCausedInBeingByAnother`: some being other than x causes x's
  being. The broad gloss.

With `Creature := IsCreatureOfUniversalCause`, the existing statement
`CausedInBeingByAnotherIsCreature` says exactly: whatever is CREATURE_2 is
CREATURE_1 (`causedInBeingByAnotherIsCreature_iff`). That is the passage between
the senses. It is no longer bare: the results module derives it from the
existing proved Fourth-Way consequence `MaximalCauseWithNoDistinctEsseCause`
(some maximum in being causes the being of every other being in act, and no
being distinct from it causes its being) and one weak premise
(`CausedEsseIsHad`: what has its being caused is in act as to being), and then
derives the bridge `CausedEsseIsReceived` of the unified Dei Filius route from it
and `CreatureEsseIsReceived` read at CREATURE_1.

Analyst formulations, attribution deferred. SCOPE CONDITION (definition
`80dea550`): elements of the domain are individuated by their act of being, so
the divine processions are no instances of `CausesIn c x esse` with `c ≠ x`. -/

@[expose] public section

namespace TruthCore.Causality.CreatureSenses

open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus IsMaximumIn)
open TruthCore.Case.Catholicism (MaximalCauseWithNoDistinctEsseCause)
open TruthCore.Causality.Round2PerfectionPrimacy
  (CausedInBeingByAnotherIsCreature CreatureEsseIsReceived)
open TruthCore.Causality.CausalMapsBatch1 (CausedPerfectionIsHad)
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)

section Vocabulary

variable {B R P : Type}

/-- CREATURE_1 (`DEF-CREATURE`, narrow): x is ordered to God as to its principle
and cause, with God read as a universal cause of being. Some g other than x
causes the being of every other being in act (`CausesAllInGenus InAct CausesIn
esse g`) and causes x's being. Example: on the stage-two route, any being other
than the maximum, whose being the maximum causes. Counterexample: a being caused
only by a cause that is not a cause of the being of everything else, where no
universal cause causes it. -/
def IsCreatureOfUniversalCause (InAct : B → R → Prop) (CausesIn : B → B → R → Prop)
    (esse : R) (x : B) : Prop :=
  ∃ g, CausesAllInGenus InAct CausesIn esse g ∧ x ≠ g ∧ CausesIn g x esse

/-- CREATURE_2 (broad): some being other than x causes x's being, a secondary
cause included. -/
def IsCausedInBeingByAnother (CausesIn : B → B → R → Prop) (esse : R) (x : B) : Prop :=
  ∃ c, c ≠ x ∧ CausesIn c x esse

/-- Weak version of `STMT-CAUSED-PERFECTION-IS-HAD-BY-EFFECT`, restricted to
esse: whatever has its being caused (by anything) is in act as to being. Open
premise, analyst formulation. -/
def CausedEsseIsHad (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ c x, CausesIn c x esse → InAct x esse

/-- Read at CREATURE_1, the existing premise `CausedInBeingByAnotherIsCreature`
is exactly the passage from CREATURE_2 to CREATURE_1. A presentation lemma; it
asserts neither side. -/
theorem causedInBeingByAnotherIsCreature_iff (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) :
    CausedInBeingByAnotherIsCreature CausesIn (IsCreatureOfUniversalCause InAct CausesIn esse) esse ↔
      ∀ x, IsCausedInBeingByAnother CausesIn esse x → IsCreatureOfUniversalCause InAct CausesIn esse x := by
  constructor
  · intro h x ⟨c, hne, hc⟩
    exact h c x hne hc
  · intro h c x hne hc
    exact h x ⟨c, hne, hc⟩

/-- CREATURE_1 is contained in CREATURE_2 (by definition, no premise). -/
theorem creature1_isCausedInBeingByAnother (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (x : B)
    (h : IsCreatureOfUniversalCause InAct CausesIn esse x) :
    IsCausedInBeingByAnother CausesIn esse x := by
  obtain ⟨g, _, hne, hg⟩ := h
  exact ⟨g, fun e => hne e.symm, hg⟩

end Vocabulary

/-! ## Controls -/

namespace Control

/-- Three beings. -/
inductive Three
  | a
  | b
  | c
  deriving DecidableEq

open Three

/-- (1) Separation model: every being is in act as to being, `a` causes `b`'s
being and nothing else is caused; no comparisons. Every being is maximal, no
being is a universal cause (`a` does not cause `c`), so `b` is CREATURE_2 and not
CREATURE_1. The bridge fails, `CausedEsseIsHad` holds, and so does the
maximal-uncaused part of the Fourth-Way consequence without its universal cause:
that consequence fails here. -/
abbrev sepInAct : Three → Unit → Prop := fun _ _ => True
abbrev sepCauses : Three → Three → Unit → Prop := fun x y _ => x = a ∧ y = b
abbrev noMore : Unit → Three → Three → Prop := fun _ _ _ => False

/-- (2) Omission model for `CausedEsseIsHad`: only `a` is in act; `b` causes
`c`'s being. `a` is maximal, causes the being of every other being in act
(vacuously) and is caused by nothing, so the Fourth-Way consequence holds, while
`c` is caused and not in act: the weak premise and the bridge fail. -/
abbrev omInAct : Three → Unit → Prop := fun x _ => x = a
abbrev omCauses : Three → Three → Unit → Prop := fun x y _ => x = b ∧ y = c

/-- (3) Nonvacuity witness on `Bool`: every being is in act, `true` causes
`false`'s being, `false`'s esse is received in the principle `()`. The
Fourth-Way consequence, `CausedEsseIsHad`, the bridge, `CreatureEsseIsReceived`
at CREATURE_1 and `CausedEsseIsReceived` all hold, and some being is caused. -/
abbrev witInAct : Bool → Unit → Prop := fun _ _ => True
abbrev witCauses : Bool → Bool → Unit → Prop := fun x y _ => x = true ∧ y = false
abbrev witMore : Unit → Bool → Bool → Prop := fun _ _ _ => False
abbrev witRecv : Bool → Unit → Prop := fun x _ => x = false

/-- The checked controls. -/
def Controls : Prop :=
  -- (1) CREATURE_2 does not give CREATURE_1 without the bridge
  (IsCausedInBeingByAnother sepCauses () b ∧
    ¬ IsCreatureOfUniversalCause sepInAct sepCauses () b ∧
    ¬ CausedInBeingByAnotherIsCreature sepCauses
      (IsCreatureOfUniversalCause sepInAct sepCauses ()) () ∧
    CausedEsseIsHad sepCauses sepInAct () ∧
    ¬ MaximalCauseWithNoDistinctEsseCause sepInAct noMore sepCauses ()) ∧
  -- (2) omitting the weak premise
  (MaximalCauseWithNoDistinctEsseCause omInAct noMore omCauses () ∧
    ¬ CausedEsseIsHad omCauses omInAct () ∧
    ¬ CausedInBeingByAnotherIsCreature omCauses
      (IsCreatureOfUniversalCause omInAct omCauses ()) ()) ∧
  -- (3) nonvacuity
  (MaximalCauseWithNoDistinctEsseCause witInAct witMore witCauses () ∧
    CausedEsseIsHad witCauses witInAct () ∧
    CausedInBeingByAnotherIsCreature witCauses
      (IsCreatureOfUniversalCause witInAct witCauses ()) () ∧
    CreatureEsseIsReceived (IsCreatureOfUniversalCause witInAct witCauses ()) witRecv ∧
    CausedEsseIsReceived witCauses () witRecv ∧
    IsCausedInBeingByAnother witCauses () false)

end Control

end TruthCore.Causality.CreatureSenses
