module

public import TruthCore.Causality.TermSenseForks3

/-! Sense forks, batch 3: per-sense theorems for "maxime ens" and "potency",
the sense bridges, the optional joint summaries and the controls.
Analyst formulations, attribution deferred. -/

@[expose] public section

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
  obtain ⟨m, hm⟩ := hSome
  exact ⟨m, hm, hCauses m hm⟩

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
  obtain ⟨m, hm⟩ := hSome
  exact ⟨m, hBridge m hm, hCauses m hm⟩

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
  obtain ⟨m, hm⟩ := hSome
  exact ⟨m, hBridge m hm, hCauses m hm⟩

/-- Sense bridge MAXIME_2 → MAXIME_1 derived: if whatever is more a being than
`m` has being and a strictly higher degree, a greatest-degree bearer of being
is maximal in being. -/
theorem greatestInBeingIsMaximal {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree)
    (hTracks : MoreInBeingTracksDegree InAct MoreIn esse value) :
    GreatestInBeingIsMaximal InAct MoreIn esse value := by
  intro m hm
  refine ⟨hm.1, fun y hy => ?_⟩
  obtain ⟨hyAct, hlt⟩ := hTracks y m hy
  have hle : value y ≤ value m := hm.2.2 ⟨y, hyAct, rfl⟩
  exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

/-- Sense bridge MAXIME_3 → MAXIME_1 derived: if being more such is
asymmetric, what is more a being than every other thing is maximal in being. -/
theorem strictlyGreatestInBeingIsMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (hAsym : MoreInIsAsymmetric MoreIn) :
    StrictlyGreatestInBeingIsMaximal InAct MoreIn esse := by
  intro m hm
  refine ⟨hm.1, fun y hy => ?_⟩
  have hne : y ≠ m := fun h => by
    subst h
    exact hAsym esse y y hy hy
  exact hAsym esse m y (hm.2 y hne) hy

/-- MAXIME_1 for the causal principle, at the root-route node: the principle
that what is MAXIMAL in a genus causes all in the genus, instantiated at being. -/
theorem maximumInBeingCausesAllMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse :=
  fun m hm => hGenus esse m hm

/-- MAXIME_3 for the causal principle, at the root-route node: what is STRICTLY
greatest in being causes being in all others, and (sense bridge) what is
MAXIMAL in being is STRICTLY greatest. -/
theorem maximumInBeingCausesAllStrict {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hCauses : StrictlyGreatestInBeingCausesAllBeings InAct MoreIn CausesIn esse)
    (hBridge : MaximalInBeingIsStrictlyGreatest InAct MoreIn esse) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse :=
  fun m hm => hCauses m (hBridge m hm)

/-- Sense bridge MAXIME_1 → MAXIME_3 derived: if any two distinct things are
comparable in being, a MAXIMAL being is STRICTLY greatest. -/
theorem maximalInBeingIsStrictlyGreatest {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (hConn : MoreInBeingConnected MoreIn esse) :
    MaximalInBeingIsStrictlyGreatest InAct MoreIn esse := by
  intro m hm
  refine ⟨hm.1, fun x hx => ?_⟩
  exact (hConn x m hx).elim (fun h => absurd h (hm.2 x)) id

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
  have hAgree : UsesAgree use :=
    usesAgree_of_cover_unique (MaximeBy InAct MoreIn esse value) Select use hCover hUnique
  obtain ⟨m, hm⟩ := hSome
  have hmc : use .causal m := by rw [hAgree .causal .existence]; exact hm
  obtain ⟨σ, -, hσ⟩ := hCover .existence
  have hmσ : MaximeBy InAct MoreIn esse value σ m := by rw [← hσ]; exact hm
  refine ⟨m, ?_, hCauses m hmc⟩
  cases σ with
  | maximal => exact hmσ
  | greatestDegree => exact hGreatest m hmσ
  | strict => exact hStrict m hmσ

/-! ## "potency": one theorem per sense -/

/-- POTENCY_1 (adopted): what is moved has the capacity without the act, and
a mover is in act; so nothing moves itself in the respect in which it is moved.
No separate non-simultaneity premise: the adopted definition contains it. -/
theorem noSelfMotionAdoptedPotency {Being Respect : Type}
    (InAct CanBe MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hPot : MovedOnlyAsInAdoptedPotency MovedIn InAct CanBe)
    (hAct : MovesOnlyAsInActReading MovesIn InAct) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn :=
  fun x r hMoved hMoves => (hPot x r hMoved).2 (hAct x x r hMoves)

/-- POTENCY_3 (capacity): what is moved has the capacity, a mover is in act,
and nothing in act has the capacity for that act. -/
theorem noSelfMotionCapacity {Being Respect : Type}
    (InAct CanBe MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hPot : MovedOnlyAsCapable MovedIn CanBe)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNon : NothingActualAndCapable InAct CanBe) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn :=
  fun x r hMoved hMoves => hNon x r ⟨hAct x x r hMoves, hPot x r hMoved⟩

/-- The CAPACITY non-simultaneity fails once some capacity is retained in
exercise. -/
theorem capacityNonSimultaneityFails {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) (h : SomeCapacityExercised InAct CanBe) :
    CapacityNonSimultaneityFails InAct CanBe := by
  intro hNon
  obtain ⟨x, r, hx⟩ := h
  exact hNon x r hx

/-- The Megarian thesis (ability only when acting), with some capacity, gives a
capacity retained in exercise: Aristotle and the Megarians agree that the
CAPACITY non-simultaneity fails. -/
theorem capacityExercisedFromMegarian {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop)
    (hMeg : MegarianAbilityOnlyWhenActingReading InAct CanBe)
    (hSome : SomethingHasACapacity CanBe) :
    SomeCapacityExercised InAct CanBe := by
  obtain ⟨x, r, hx⟩ := hSome
  exact ⟨x, r, hMeg x r hx, hx⟩

/-- Strength order: moved only as in adopted potency implies moved only as
capable. -/
theorem movedOnlyAsCapableFromAdopted {Being Respect : Type}
    (MovedIn InAct CanBe : Being → Respect → Prop)
    (h : MovedOnlyAsInAdoptedPotency MovedIn InAct CanBe) :
    MovedOnlyAsCapable MovedIn CanBe :=
  fun x r hx => (h x r hx).1

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
  have hAgree : UsesAgree use :=
    usesAgree_of_cover_unique (PotencyBy InAct CanBe InPotency) Select use hCover hUnique
  intro x r hMoved hMoves
  have h1 : use .moved x r := hPot x r hMoved
  rw [hAgree .moved .nonSimultaneity] at h1
  exact hNon x r ⟨hAct x x r hMoves, h1⟩

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

/-- Incomparable represented degrees: no greatest degree among both beings. -/
private theorem noGreatestIncomparable (m : Bool) :
    ¬ @GreatestDegreeBearer Bool Unit Bool discretePreorder
      (fun (_ : Bool) (_ : Unit) => True) () (fun x => x) m := by
  rintro ⟨-, -, hub⟩
  have h := hub ⟨!m, trivial, rfl⟩
  cases m
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h

theorem termSenseForks3Controls : TermSenseForks3Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- maxime: coverage without exclusivity
    refine ⟨Bool, discretePreorder, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => False, fun x => x,
      fun σ => σ = .maximal ∨ σ = .greatestDegree,
      fun u => match u with
        | .existence => IsMaximalIn (fun (_ : Bool) (_ : Unit) => True) (fun _ _ _ => False) ()
        | .causal => @GreatestDegreeBearer Bool Unit Bool discretePreorder
            (fun (_ : Bool) (_ : Unit) => True) () (fun x => x),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      cases u
      · exact ⟨.maximal, Or.inl rfl, rfl⟩
      · exact ⟨.greatestDegree, Or.inr rfl, rfl⟩
    · intro h
      exact absurd (h .maximal .greatestDegree (Or.inl rfl) (Or.inr rfl)) (by decide)
    · exact ⟨true, trivial, fun _ h => h⟩
    · intro m hm
      exact absurd hm (noGreatestIncomparable m)
    · exact @greatestInBeingIsMaximal _ _ _ discretePreorder _ _ _ _ (fun _ _ h => h.elim)
    · exact strictlyGreatestInBeingIsMaximal _ _ _ (fun _ _ _ h => h.elim)
    · rintro ⟨m, -, hc⟩
      exact hc (!m) (by cases m <;> decide) trivial
  · -- maxime: coverage fails
    refine ⟨Unit, onePreorder, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => False, fun _ => (), fun σ => σ = .maximal,
      fun u => match u with
        | .existence => fun m => m = true
        | .causal => fun _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hCover
      obtain ⟨σ, -, hσ⟩ := hCover .existence
      cases σ with
      | maximal =>
        have h := Iff.of_eq (congrFun hσ false)
        exact absurd (h.mpr ⟨trivial, fun _ h => h⟩) (by decide)
      | greatestDegree =>
        have h := Iff.of_eq (congrFun hσ false)
        exact absurd (h.mpr ⟨trivial, ⟨false, trivial, rfl⟩, fun _ _ => trivial⟩) (by decide)
      | strict =>
        have h := Iff.of_eq (congrFun hσ true)
        exact (h.mp rfl).2 false (by decide)
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · exact ⟨true, rfl⟩
    · intro _ h
      exact h.elim
    · exact @greatestInBeingIsMaximal _ _ _ onePreorder _ _ _ _ (fun _ _ h => h.elim)
    · exact strictlyGreatestInBeingIsMaximal _ _ _ (fun _ _ _ h => h.elim)
    · rintro ⟨m, -, hc⟩
      exact hc (!m) (by cases m <;> decide) trivial
  · -- maxime: nonvacuity
    refine ⟨Bool, twoPreorder, fun _ _ => True, fun _ y m => y = true ∧ m = false,
      fun c _ _ => c = true, fun x => x, fun σ => σ = .maximal,
      fun _ => IsMaximalIn (fun (_ : Bool) (_ : Unit) => True)
        (fun _ y m => y = true ∧ m = false) (),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      exact ⟨.maximal, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · exact ⟨true, trivial, fun _ h => Bool.noConfusion h.2⟩
    · intro m hm x _ _
      cases m with
      | true => rfl
      | false => exact absurd ⟨rfl, rfl⟩ (hm.2 true)
    · refine @greatestInBeingIsMaximal _ _ _ twoPreorder _ _ _ _ ?_
      rintro y m ⟨rfl, rfl⟩
      exact ⟨trivial, Or.inl rfl, fun h => h.elim Bool.noConfusion Bool.noConfusion⟩
    · refine strictlyGreatestInBeingIsMaximal _ _ _ ?_
      rintro _ x y ⟨rfl, rfl⟩ ⟨h, -⟩
      exact Bool.false_ne_true h
    · exact ⟨true, ⟨trivial, fun _ h => Bool.noConfusion h.2⟩, fun _ _ _ => rfl⟩
    · exact ⟨true, false, by decide⟩
  · -- maxime: GREATEST_DEGREE branch without its bridge
    refine ⟨Unit, onePreorder, fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True,
      fun _ => (), ?_, ?_, ?_⟩
    · exact ⟨true, trivial, ⟨true, trivial, rfl⟩, fun _ _ => trivial⟩
    · intro _ _ _ _ _
      trivial
    · rintro ⟨m, hm, -⟩
      exact hm.2 m trivial
  · -- maxime: STRICT branch without its bridge
    refine ⟨fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True, ?_, ?_, ?_⟩
    · exact ⟨true, trivial, fun _ _ => trivial⟩
    · intro _ _ _ _ _
      trivial
    · rintro ⟨m, hm, -⟩
      exact hm.2 m trivial
  · -- maxime: STRICT causal principle without its bridge
    refine ⟨fun _ _ => True, fun _ _ _ => False, fun _ _ _ => False, ?_, ?_⟩
    · rintro m ⟨-, hm⟩
      exact absurd (hm (!m) (by cases m <;> decide)) id
    · intro h
      exact h true ⟨trivial, fun _ h => h⟩ false (by decide) trivial
  · -- maxime: tied maxima
    refine ⟨fun _ _ => True, fun _ _ _ => False, fun _ _ _ h => h.elim,
      ⟨true, trivial, fun _ h => h⟩, ?_⟩
    rintro ⟨m, -, hm⟩
    exact hm (!m) (by cases m <;> decide)
  · -- potency: coverage without exclusivity
    refine ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => True,
      fun _ _ _ => True, fun σ => σ = .adopted ∨ σ = .capacity,
      fun u => match u with
        | .moved => CapacityPotency (fun (_ : Unit) (_ : Unit) => True)
        | .nonSimultaneity => AdoptedPotency.InPotency (fun (_ : Unit) (_ : Unit) => True)
            (fun _ _ => True),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      cases u
      · exact ⟨.capacity, Or.inr rfl, rfl⟩
      · exact ⟨.adopted, Or.inl rfl, rfl⟩
    · intro h
      exact absurd (h .adopted .capacity (Or.inl rfl) (Or.inr rfl)) (by decide)
    · intro _ _ _
      trivial
    · intro _ _ _ _
      trivial
    · intro _ _ h
      exact h.2.2 h.1
    · intro h
      exact h () () trivial trivial
  · -- potency: coverage fails
    refine ⟨fun _ _ => True, fun _ _ => False, fun _ _ => False, fun _ _ => True,
      fun _ _ _ => True, fun σ => σ = .independent,
      fun u => match u with
        | .moved => fun _ _ => True
        | .nonSimultaneity => fun _ _ => False,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hCover
      obtain ⟨σ, -, hσ⟩ := hCover .moved
      have h := congrFun (congrFun hσ ()) ()
      cases σ with
      | adopted => exact ((Iff.of_eq h).mp trivial).1
      | independent => exact (Iff.of_eq h).mp trivial
      | capacity => exact (Iff.of_eq h).mp trivial
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · intro _ _ _
      trivial
    · intro _ _ _ _
      trivial
    · intro _ _ h
      exact h.2
    · intro h
      exact h () () trivial trivial
  · -- potency: nonvacuity
    refine ⟨fun x _ => x = true, fun _ _ => True, fun x _ => x = false,
      fun x _ => x = false, fun y x _ => y = true ∧ x = false,
      fun σ => σ = .independent, fun _ => fun x _ => x = false,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      exact ⟨.independent, rfl, rfl⟩
    · intro σ τ hσ hτ
      exact hσ.trans hτ.symm
    · intro _ _ h
      exact h
    · intro _ _ _ h
      exact h.1
    · rintro x _ ⟨h1, h2⟩
      exact Bool.false_ne_true (h2.symm.trans h1)
    · rintro x _ hx ⟨h1, -⟩
      exact Bool.false_ne_true (hx.symm.trans h1)
    · exact ⟨true, false, (), rfl, rfl⟩
  · -- potency, ADOPTED: omit the mover-in-act premise
    refine ⟨fun _ _ => False, fun _ _ => True, fun _ _ => True, fun _ _ _ => True, ?_, ?_⟩
    · intro _ _ _
      exact ⟨trivial, fun h => h⟩
    · intro h
      exact h () () trivial trivial
  · -- potency, ADOPTED: omit the adopted moved premise
    refine ⟨fun _ _ => True, fun _ _ => True, fun _ _ _ => True, ?_, ?_⟩
    · intro _ _ _ _
      trivial
    · intro h
      exact h () () trivial trivial

end TruthCore.Results.Causality.TermSenseForks3
