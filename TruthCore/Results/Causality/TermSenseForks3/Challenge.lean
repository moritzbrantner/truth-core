import TruthCore.Causality.TermSenseForks3

/-! Sense forks, batch 3: per-sense theorems for "maxime ens" and "potency",
the sense bridges, the optional joint summaries and the controls.
Analyst formulations, attribution deferred. -/

namespace TruthCore.Results.Causality.TermSenseForks3

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.GodMaximalCausal (MoreInIsAsymmetric)
open TruthCore.Alternatives.ActPotencyRegress (MegarianAbilityOnlyWhenActingReading)

/-! ## "maxime ens": one theorem per sense -/

/-- MAXIME_1 (maximal): some being is maximal in being, and whatever is maximal
in being causes being in every other being; so some maximal being causes being
in every other being. -/
theorem maximeEnsCausesAllMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hSome : SomeBeingMaximalInBeing InAct MoreIn esse)
    (hCauses : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-- MAXIME_2 (greatest represented degree): some being has the greatest degree
of being, a greatest-degree bearer of a perfection causes it in every other
bearer, and (sense bridge) a greatest-degree bearer of being is maximal in
being. -/
theorem maximeEnsCausesAllGreatestDegree {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (value : Being → Degree)
    (hSome : SomeBeingGreatestInBeing InAct esse value)
    (hCauses : GreatestDegreeCausesAllInGenusReading InAct CausesIn esse value)
    (hBridge : GreatestInBeingIsMaximal InAct MoreIn esse value) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-- MAXIME_3 (strict supremacy): some being is more a being than every other
thing, such a being causes being in every other being, and (sense bridge) it
is maximal in being. -/
theorem maximeEnsCausesAllStrict {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hSome : SomeBeingStrictlyGreatestInBeing InAct MoreIn esse)
    (hCauses : StrictlyGreatestInBeingCausesAllBeings InAct MoreIn CausesIn esse)
    (hBridge : StrictlyGreatestInBeingIsMaximal InAct MoreIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-- Sense bridge MAXIME_2 → MAXIME_1 derived: if whatever is more a being than
`m` has being and a strictly higher degree, a greatest-degree bearer of being
is maximal in being. -/
theorem greatestInBeingIsMaximal {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree)
    (hTracks : MoreInBeingTracksDegree InAct MoreIn esse value) :
    GreatestInBeingIsMaximal InAct MoreIn esse value := by
  sorry

/-- Sense bridge MAXIME_3 → MAXIME_1 derived: if being more such is
asymmetric, what is more a being than every other thing is maximal in being. -/
theorem strictlyGreatestInBeingIsMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (hAsym : MoreInIsAsymmetric MoreIn) :
    StrictlyGreatestInBeingIsMaximal InAct MoreIn esse := by
  sorry

/-- MAXIME_1 for the causal principle, at the root-route node: the principle
that what is MAXIMAL in a genus causes all in the genus, instantiated at being. -/
theorem maximumInBeingCausesAllMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  sorry

/-- MAXIME_3 for the causal principle, at the root-route node: what is STRICTLY
greatest in being causes being in all others, and (sense bridge) what is
MAXIMAL in being is STRICTLY greatest. -/
theorem maximumInBeingCausesAllStrict {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hCauses : StrictlyGreatestInBeingCausesAllBeings InAct MoreIn CausesIn esse)
    (hBridge : MaximalInBeingIsStrictlyGreatest InAct MoreIn esse) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  sorry

/-- Sense bridge MAXIME_1 → MAXIME_3 derived: if any two distinct things are
comparable in being, a MAXIMAL being is STRICTLY greatest. -/
theorem maximalInBeingIsStrictlyGreatest {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (hConn : MoreInBeingConnected MoreIn esse) :
    MaximalInBeingIsStrictlyGreatest InAct MoreIn esse := by
  sorry

/-- Optional summary over MAXIME_1-3. Coverage reads both uses of the
superlative (existence, causal) in selected senses; exclusivity makes them one
sense; whichever it is, the witness of the existence use causes being in every
other being, and it is maximal in being directly or through the sense bridge. -/
theorem maximeEnsCausesAllBySenseFork {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (value : Being → Degree)
    (Select : MaximeSense → Prop) (use : MaximeUse → Being → Prop)
    (hCover : MaximeSensesExhaustive InAct MoreIn esse value Select use)
    (hUnique : MaximeSenseUnique Select)
    (hSome : SomeMaximeInRouteSense use)
    (hCauses : RouteMaximeCausesAllBeings InAct CausesIn esse use)
    (hGreatest : GreatestInBeingIsMaximal InAct MoreIn esse value)
    (hStrict : StrictlyGreatestInBeingIsMaximal InAct MoreIn esse) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-! ## "potency": one theorem per sense -/

/-- POTENCY_1 (adopted): what is moved has the capacity without the act, and
a mover is in act; so nothing moves itself in the respect in which it is moved.
No separate non-simultaneity premise: the adopted definition contains it. -/
theorem noSelfMotionAdoptedPotency {Being Respect : Type}
    (InAct CanBe MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hPot : MovedOnlyAsInAdoptedPotency MovedIn InAct CanBe)
    (hAct : MovesOnlyAsInActReading MovesIn InAct) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn := by
  sorry

/-- POTENCY_3 (capacity): what is moved has the capacity, a mover is in act,
and nothing in act has the capacity for that act. -/
theorem noSelfMotionCapacity {Being Respect : Type}
    (InAct CanBe MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hPot : MovedOnlyAsCapable MovedIn CanBe)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNon : NothingActualAndCapable InAct CanBe) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn := by
  sorry

/-- The CAPACITY non-simultaneity fails once some capacity is retained in
exercise. -/
theorem capacityNonSimultaneityFails {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) (h : SomeCapacityExercised InAct CanBe) :
    CapacityNonSimultaneityFails InAct CanBe := by
  sorry

/-- The Megarian thesis (ability only when acting), with some capacity, gives a
capacity retained in exercise: Aristotle and the Megarians agree that the
CAPACITY non-simultaneity fails. -/
theorem capacityExercisedFromMegarian {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop)
    (hMeg : MegarianAbilityOnlyWhenActingReading InAct CanBe)
    (hSome : SomethingHasACapacity CanBe) :
    SomeCapacityExercised InAct CanBe := by
  sorry

/-- Strength order: moved only as in adopted potency implies moved only as
capable. -/
theorem movedOnlyAsCapableFromAdopted {Being Respect : Type}
    (MovedIn InAct CanBe : Being → Respect → Prop)
    (h : MovedOnlyAsInAdoptedPotency MovedIn InAct CanBe) :
    MovedOnlyAsCapable MovedIn CanBe := by
  sorry

/-- Optional summary over POTENCY_1-3. Coverage reads both uses of "in
potency" in selected senses; exclusivity makes them one sense; whichever it is,
a self-mover would be in potency in that one sense and in act, which the
non-simultaneity use excludes. -/
theorem noSelfMotionByPotencySenseFork {Being Respect : Type}
    (InAct CanBe InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (Select : PotencySense → Prop) (use : PotencyUse → Being → Respect → Prop)
    (hCover : PotencySensesExhaustive InAct CanBe InPotency Select use)
    (hUnique : PotencySenseUnique Select)
    (hPot : MovedOnlyAsInPotencyReading MovedIn (use .moved))
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNon : NotActAndPotencyInSameRespectReading InAct (use .nonSimultaneity)) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn := by
  sorry

/-! ## Controls -/

/-- Control degree orders, hand-written so that the controls stay axiom-free
(Mathlib's order instances on `Bool`, products and `Unit` carry `propext` in
their proof fields). They are plain definitions, passed explicitly.
`discretePreorder`: two incomparable degrees. -/
@[instance_reducible] def discretePreorder : Preorder Bool where
  le x y := x = y
  lt x y := x = y ∧ ¬ y = x
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- One degree, shared by every bearer (ties). -/
@[instance_reducible] def onePreorder : Preorder Unit where
  le _ _ := True
  lt _ _ := True ∧ ¬ True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Two degrees, `false` below `true`. -/
@[instance_reducible] def twoPreorder : Preorder Bool where
  le x y := x = false ∨ y = true
  lt x y := (x = false ∨ y = true) ∧ ¬ (y = false ∨ x = true)
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  lt_iff_le_not_ge _ _ := Iff.rfl

theorem termSenseForks3Controls : TermSenseForks3Controls := by
  sorry

end TruthCore.Results.Causality.TermSenseForks3
