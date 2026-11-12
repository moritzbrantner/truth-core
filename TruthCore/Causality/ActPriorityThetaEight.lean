module

public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-! Act's priority at a first being from *Metaphysics* Θ.8 (analyst
reconstructions, attribution deferred)

`ActPriorityAtFirst` reduced the routes' use of act priority to the q.3 a.1
conclusion that a first being is in potency in no respect
(`FirstBeingIsInNoWayInPotencyReading`), and derived it by composition from
five open premises. This module asks which of the Θ.8 priorities of act
(1049b4-1051a3: in definition, in time, in substance) gives that conclusion, or
the composition route's two analyst premises `FirstBeingIsInSomeAct` and
`ActAndPotencyMakeComposite`, and from what.

* **Definition (1049b12-17).** Potency is said by reference to its act. In this
  vocabulary that is built into the typing: `InPotency x r` and `InAct y r`
  share the respect `r`. It constrains no being, so it derives nothing here.
* **Time (1049b17-1050a3).** What passes from potency to act does so by
  something in act; recorded attempts show it reaches only potencies being
  actualized, and is vacuous at a first being's idle potency.
* **Substance, the eternal (1050b6-19).** Read with *In Metaph.* IX lect. 9,
  it excludes a first being's potency in the respect of being only
  (`ActPriorFromIncorruptibleFacts`). Here it gives `FirstBeingIsInSomeAct`
  from the incorruptibility of first beings (`FirstBeingIsIncorruptibleSimply`)
  and the sourced reading that incorruptible beings are in act in substance;
  with the composition premise restricted to beings in act in being
  (`ActInBeingAndPotencyMakeComposite`) it gives the q.3 a.1 conclusion.
* **Substance, potency for the sake of act (1050a4-b2).** An unrealized
  potency is for the sake of an act it never has. Read with the tertia via's
  plenitude premise (a possibility never realized in an infinite past is no
  possibility), a first being's potency was once actualized; its loss then
  needs another efficient cause, which is prior to it. This route uses no
  composition premise and no cause of composites (`PotencyMakesActPossible`,
  `ActThenPotencyHasAnotherCause`).

Time is a supplied carrier with a supplied `Before`; `InActAt t` and
`InPotencyAt t` are the act and independent potency parameters at `t`. Simple
priority and efficient causation are not time-indexed: simple priority is
priority by nature (`DEF-SIMPLE-PRIORITY`), and `EfficientlyCausesIn c x s`
says that `c` efficiently causes `x` in `s`, at some time.
-/

@[expose] public section

namespace TruthCore.Causality.ActPriorityThetaEight

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Causality.ActPriorityAtFirst

/-- OPEN, analyst formulation, unattributed: every first being is simply
incorruptible, that is, cannot fail to be in the respect of being (`esse`).
Θ.8, 1050b16-19 (*Met.*) holds that the eternal is prior in substance and that
the necessary beings are first; read here only as the claim that a first being
cannot fail to be, not that it cannot be otherwise in any respect. Its denial is
a contingent first being. -/
def FirstBeingIsIncorruptibleSimply {B R : Type} (CanFailToBe : B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ f, IsFirstBeing PriorSimply f → IncorruptibleSimply CanFailToBe esse f

/-- OPEN, analyst formulation, unattributed: whatever is in act in the respect
of being and in potency in some respect is composite. It is the instance of
`ActAndPotencyMakeComposite` at the respect `esse`: the actual being and an
unrealized capacity are two principles of one thing. Given
`ActualityOnlyInsofarAsBeingReading` the two are equivalent (`Control.Facts`). -/
def ActInBeingAndPotencyMakeComposite {B R : Type} (InAct InPotency : B → R → Prop) (esse : R)
    (Composite : B → Prop) : Prop :=
  ∀ x r, InAct x esse → InPotency x r → Composite x

/-- OPEN, analyst formulation, unattributed: whatever is in potency in a respect
at some time can be in act in that respect: the condition "being in act in that
respect" on times is possible in the supplied `Possible` sense. *Met.* Θ.3,
1047a24-26 and Θ.8, 1049b12-17 (a potency is a potency for its act) are
orientation only. `Possible` is the predicate on time-conditions of the tertia
via's plenitude reading. -/
def PotencyMakesActPossible {B R T : Type} (InActAt InPotencyAt : T → B → R → Prop)
    (Possible : (T → Prop) → Prop) : Prop :=
  ∀ t x r, InPotencyAt t x r → Possible (fun t' => InActAt t' x r)

/-- OPEN, analyst formulation, unattributed: whatever was in act in a respect
and is later in potency in it has an efficient cause other than itself, in some
respect. With non-overlap the later potency is a loss of the act, a change, and
the premise generalizes "whatever is moved is moved by another" to that change;
without non-overlap it also covers a being that keeps the act and gains the
potency. -/
def ActThenPotencyHasAnotherCause {B R T : Type} (Before : T → T → Prop)
    (InActAt InPotencyAt : T → B → R → Prop) (EfficientlyCausesIn : B → B → R → Prop) :
    Prop :=
  ∀ t' t x r, Before t' t → InActAt t' x r → InPotencyAt t x r →
    ∃ c s, c ≠ x ∧ EfficientlyCausesIn c x s

namespace Control

/-! Interpretations. Beings and respects are over `Bool`: the being `true` is a
ground, `false` a stone or a first body; the respect `true` is being (`esse`),
`false` a place. Times are `Int` with `now = 0` and `Before := (· < ·)`. -/

/-- In act exactly in being. -/
def esseAct (_ : Bool) (r : Bool) : Prop := r = true
/-- In potency exactly to the place. -/
def placePotency (_ : Bool) (r : Bool) : Prop := r = false
/-- Can fail to be exactly in the place. -/
def placeCanFail (_ : Bool) (r : Bool) : Prop := r = false
/-- Can fail to be in every respect. -/
def allCanFail (_ : Bool) (_ : Bool) : Prop := True
/-- Nothing is simply prior to anything. -/
def noPrior (_ _ : Bool) : Prop := False
/-- Nothing causes anything. -/
def noCause (_ _ _ : Bool) : Prop := False
/-- Everything is composite. -/
def allComposite (_ : Bool) : Prop := True
/-- In act exactly in the place, and not in being. -/
def placeAct (_ : Bool) (r : Bool) : Prop := r = false
/-- In potency exactly in being. -/
def essePotency (_ : Bool) (r : Bool) : Prop := r = true
/-- Nothing is composite. -/
def noComposite (_ : Bool) : Prop := False

/-- Heavenly first being: the Θ.8 substance readings (every potency of the
contradictory, the incorruptible in act in substance), the incorruptibility of
first beings, being in act in some respect, the composition-free part of the
picture and non-overlap all hold, with a first being in potency to a place; so
act priority at a first being fails. Θ.8's substance argument, without a
composition premise, does not reach the weak version. -/
def HeavenlyFirst : Prop :=
  PotencyIsOfContradictionReading placePotency placeCanFail ∧
  IncorruptibleIsInActReading esseAct placeCanFail true ∧
  FirstBeingIsIncorruptibleSimply placeCanFail true noPrior ∧
  FirstBeingIsInSomeAct esseAct noPrior ∧
  NotActAndPotencyInSameRespectReading esseAct placePotency ∧
  IsFirstBeing noPrior false ∧ placePotency false false ∧
  ¬ FirstBeingActPriority esseAct placePotency noPrior

/-- Contingent first being: every first being is in act in some respect, while
no first being is simply incorruptible. The Θ.8 premise used to derive
`FirstBeingIsInSomeAct` is not implied by it. -/
def ContingentFirst : Prop :=
  FirstBeingIsInSomeAct esseAct noPrior ∧
  ¬ FirstBeingIsIncorruptibleSimply allCanFail true noPrior

/-- Strictness of the restricted composition premise: a being in act in a place
but not in being, in potency in being and simple, satisfies the restricted
premise and falsifies `ActAndPotencyMakeComposite`; the same interpretation
falsifies `ActualityOnlyInsofarAsBeingReading`. -/
def RestrictedStrict : Prop :=
  ActInBeingAndPotencyMakeComposite placeAct essePotency true noComposite ∧
  ¬ ActAndPotencyMakeComposite placeAct essePotency noComposite ∧
  ¬ ActualityOnlyInsofarAsBeingReading placeAct true

/-- Time-indexed act in being only, at every time. -/
def esseActAt (_ : Int) (_ : Bool) (r : Bool) : Prop := r = true
/-- Time-indexed potency to the place, at every time. -/
def placePotencyAt (_ : Int) (_ : Bool) (r : Bool) : Prop := r = false
/-- Every condition on times is possible. -/
def allPossible (_ : Int → Prop) : Prop := True

/-- Idle uncaused composite first being: one interpretation satisfies, at
`now = 0`, every premise of the three routes to the q.3 a.1 conclusion except
the cause of composites and plenitude: first beings in act in some respect and
simply incorruptible; incorruptible beings in act in substance; every potency of
the contradictory; act and potency make composite (both versions); causing
another's perfection is efficient; efficient causes are prior; the past is
infinite; potency makes act possible; act then potency has another cause;
non-overlap. The cause of composites fails, plenitude fails, and a first being
is composite, uncaused and in potency to a place at every time, which it never
actualizes. -/
def IdleUncausedComposite : Prop :=
  FirstBeingIsInSomeAct (esseActAt 0) noPrior ∧
  FirstBeingIsIncorruptibleSimply placeCanFail true noPrior ∧
  IncorruptibleIsInActReading (esseActAt 0) placeCanFail true ∧
  PotencyIsOfContradictionReading (placePotencyAt 0) placeCanFail ∧
  ActAndPotencyMakeComposite (esseActAt 0) (placePotencyAt 0) allComposite ∧
  ActInBeingAndPotencyMakeComposite (esseActAt 0) (placePotencyAt 0) true allComposite ∧
  TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
    noCause noCause ∧
  EfficientCauseIsPriorToEffectReading noCause noPrior ∧
  PastIsInfinite (· < ·) (0 : Int) ∧
  PotencyMakesActPossible esseActAt placePotencyAt allPossible ∧
  ActThenPotencyHasAnotherCause (· < ·) esseActAt placePotencyAt noCause ∧
  NotActAndPotencyInSameRespectReading (esseActAt 0) (placePotencyAt 0) ∧
  ¬ CompositeHasAUnitingCauseReading allComposite noCause true ∧
  ¬ PlenitudeOverInfinitePastReading (· < ·) (0 : Int) allPossible ∧
  IsFirstBeing noPrior false ∧ allComposite false ∧
  (∀ t, placePotencyAt t false false ∧ ¬ esseActAt t false false) ∧
  ¬ FirstBeingIsInNoWayInPotencyReading (placePotencyAt 0) noPrior

/-- Each premise of the Θ.8 composition route is needed (models found by
`scripts/countermodel.py`, rechecked here): dropping one leaves the other five
and a first being in potency. One respect, which is being. (1) Without
incorruptibility of first beings: everything can fail to be and is in act in
nothing. (2) Without act of the incorruptible: an incorruptible first being in
act in nothing. (3) Without the restricted composition premise: a simple being
in act and in potency in being. (4) Without the cause of composites: an uncaused
composite. (5) Without the bridge: a composite caused, not efficiently. (6)
Without efficient-cause priority: a composite efficiently caused by another,
nothing prior. -/
def ThetaEightOmissions : Prop :=
  (¬ FirstBeingIsIncorruptibleSimply (fun (_ : Fin 1) (_ : Fin 1) => True) 0
      (fun _ _ => False) ∧
    IncorruptibleIsInActReading (fun (_ : Fin 1) (_ : Fin 1) => False) (fun _ _ => True) 0 ∧
    ActInBeingAndPotencyMakeComposite (fun (_ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => True) 0 (fun _ => False) ∧
    CompositeHasAUnitingCauseReading (fun (_ : Fin 1) => False)
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) 0 ∧
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => False)) ∧
  (FirstBeingIsIncorruptibleSimply (fun (_ : Fin 1) (_ : Fin 1) => False) 0
      (fun _ _ => False) ∧
    ¬ IncorruptibleIsInActReading (fun (_ : Fin 1) (_ : Fin 1) => False) (fun _ _ => False) 0 ∧
    ActInBeingAndPotencyMakeComposite (fun (_ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => True) 0 (fun _ => False) ∧
    CompositeHasAUnitingCauseReading (fun (_ : Fin 1) => False)
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) 0 ∧
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => False)) ∧
  (FirstBeingIsIncorruptibleSimply (fun (_ : Fin 1) (_ : Fin 1) => False) 0
      (fun _ _ => False) ∧
    IncorruptibleIsInActReading (fun (_ : Fin 1) (_ : Fin 1) => True) (fun _ _ => False) 0 ∧
    ¬ ActInBeingAndPotencyMakeComposite (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => True) 0 (fun _ => False) ∧
    CompositeHasAUnitingCauseReading (fun (_ : Fin 1) => False)
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) 0 ∧
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => False)) ∧
  (FirstBeingIsIncorruptibleSimply (fun (_ : Fin 1) (_ : Fin 1) => False) 0
      (fun _ _ => False) ∧
    IncorruptibleIsInActReading (fun (_ : Fin 1) (_ : Fin 1) => True) (fun _ _ => False) 0 ∧
    ActInBeingAndPotencyMakeComposite (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => True) 0 (fun _ => True) ∧
    ¬ CompositeHasAUnitingCauseReading (fun (_ : Fin 1) => True)
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) 0 ∧
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (_ _ : Fin 1) (_ : Fin 1) => False) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Fin 1) (_ : Fin 1) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Fin 1) (_ : Fin 1) => True)
      (fun _ _ => False)) ∧
  (FirstBeingIsIncorruptibleSimply (fun (_ : Fin 2) (_ : Fin 1) => False) 0
      (fun _ _ => False) ∧
    IncorruptibleIsInActReading (fun (_ : Fin 2) (_ : Fin 1) => True) (fun _ _ => False) 0 ∧
    ActInBeingAndPotencyMakeComposite (fun (_ : Fin 2) (_ : Fin 1) => True)
      (fun x r => x = 1 ∧ r = 0) 0 (fun x => x = 1) ∧
    CompositeHasAUnitingCauseReading (fun (x : Fin 2) => x = 1)
      (fun (c x : Fin 2) (r : Fin 1) => c = 0 ∧ x = 1 ∧ r = 0) 0 ∧
    ¬ TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (c x : Fin 2) (r : Fin 1) => c = 0 ∧ x = 1 ∧ r = 0) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Fin 2) (_ : Fin 1) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (x : Fin 2) (r : Fin 1) => x = 1 ∧ r = 0)
      (fun _ _ => False)) ∧
  (FirstBeingIsIncorruptibleSimply (fun (_ : Fin 2) (_ : Fin 1) => False) 0
      (fun _ _ => False) ∧
    IncorruptibleIsInActReading (fun (_ : Fin 2) (_ : Fin 1) => True) (fun _ _ => False) 0 ∧
    ActInBeingAndPotencyMakeComposite (fun (_ : Fin 2) (_ : Fin 1) => True)
      (fun x r => x = 1 ∧ r = 0) 0 (fun x => x = 1) ∧
    CompositeHasAUnitingCauseReading (fun (x : Fin 2) => x = 1)
      (fun (c x : Fin 2) (r : Fin 1) => c = 0 ∧ x = 1 ∧ r = 0) 0 ∧
    TruthCore.Causality.Round2PerfectionPrimacy.PerfectionCausingInAnotherIsEfficient
      (fun (c x : Fin 2) (r : Fin 1) => c = 0 ∧ x = 1 ∧ r = 0)
      (fun c x r => c = 0 ∧ x = 1 ∧ r = 0) ∧
    ¬ EfficientCauseIsPriorToEffectReading (fun (c x : Fin 2) (r : Fin 1) => c = 0 ∧ x = 1 ∧ r = 0)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (x : Fin 2) (r : Fin 1) => x = 1 ∧ r = 0)
      (fun _ _ => False))

/-- Time-indexed: in act exactly before `now = 0`. -/
def actBeforeNow (t : Int) (_ : Unit) (_ : Unit) : Prop := t < 0
/-- Time-indexed: in potency exactly from `now = 0` on. -/
def potencyFromNow (t : Int) (_ : Unit) (_ : Unit) : Prop := 0 ≤ t
/-- A condition on times is possible when it was realized before `now = 0`. -/
def realizedBefore (φ : Int → Prop) : Prop := ∃ t, t < 0 ∧ φ t
/-- The stone (`false`) is in act before `now`. -/
def stoneActBefore (t : Int) (x : Bool) (_ : Unit) : Prop := x = false ∧ t < 0
/-- The stone (`false`) is in potency from `now` on. -/
def stonePotencyFrom (t : Int) (x : Bool) (_ : Unit) : Prop := x = false ∧ 0 ≤ t
/-- The ground (`true`) efficiently causes the stone. -/
def groundCausesStone (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false
/-- The ground is simply prior to the stone. -/
def groundPriorStone (y x : Bool) : Prop := y = true ∧ x = false

/-- Each premise of the plenitude route is needed, and the route is not
vacuous. Times are `Int` (or `Nat` in (2)), `now = 0`, `Before := (· < ·)`, one
respect. (1) Without plenitude: everything is possible and a being is in potency
at every time and never in act. (2) Without an infinite past (`Nat` times):
plenitude holds vacuously. (3) Without potency making act possible: nothing is
possible. (4) Without the cause of a change from act to potency: a lone being
in act before now and in potency from now on. (5) Without efficient-cause
priority: the ground causes the stone's change and is not prior. (6) Witness:
all five premises with the ground prior to the stone, a first being (the
ground) and something in potency now (the stone). -/
def PlenitudeOmissions : Prop :=
  (¬ PlenitudeOverInfinitePastReading (· < ·) (0 : Int) (fun _ => True) ∧
    PastIsInfinite (· < ·) (0 : Int) ∧
    PotencyMakesActPossible (fun (_ : Int) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ => True) ∧
    ActThenPotencyHasAnotherCause (· < ·) (fun (_ : Int) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => False)) ∧
  (PlenitudeOverInfinitePastReading (· < ·) (0 : Nat) (fun _ => True) ∧
    ¬ PastIsInfinite (· < ·) (0 : Nat) ∧
    PotencyMakesActPossible (fun (_ : Nat) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ => True) ∧
    ActThenPotencyHasAnotherCause (· < ·) (fun (_ : Nat) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => False)) ∧
  (PlenitudeOverInfinitePastReading (· < ·) (0 : Int) (fun _ => False) ∧
    PastIsInfinite (· < ·) (0 : Int) ∧
    ¬ PotencyMakesActPossible (fun (_ : Int) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ => False) ∧
    ActThenPotencyHasAnotherCause (· < ·) (fun (_ : Int) (_ : Unit) (_ : Unit) => False)
      (fun _ _ _ => True) (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => False)) ∧
  (PlenitudeOverInfinitePastReading (· < ·) (0 : Int) realizedBefore ∧
    PastIsInfinite (· < ·) (0 : Int) ∧
    PotencyMakesActPossible actBeforeNow potencyFromNow realizedBefore ∧
    ¬ ActThenPotencyHasAnotherCause (· < ·) actBeforeNow potencyFromNow
      (fun _ _ _ => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ : Unit) (_ : Unit) => False)
      (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (potencyFromNow 0) (fun _ _ => False)) ∧
  (PlenitudeOverInfinitePastReading (· < ·) (0 : Int) realizedBefore ∧
    PastIsInfinite (· < ·) (0 : Int) ∧
    PotencyMakesActPossible stoneActBefore stonePotencyFrom realizedBefore ∧
    ActThenPotencyHasAnotherCause (· < ·) stoneActBefore stonePotencyFrom groundCausesStone ∧
    ¬ EfficientCauseIsPriorToEffectReading groundCausesStone (fun _ _ => False) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (stonePotencyFrom 0) (fun _ _ => False)) ∧
  (PlenitudeOverInfinitePastReading (· < ·) (0 : Int) realizedBefore ∧
    PastIsInfinite (· < ·) (0 : Int) ∧
    PotencyMakesActPossible stoneActBefore stonePotencyFrom realizedBefore ∧
    ActThenPotencyHasAnotherCause (· < ·) stoneActBefore stonePotencyFrom groundCausesStone ∧
    EfficientCauseIsPriorToEffectReading groundCausesStone groundPriorStone ∧
    IsFirstBeing groundPriorStone true ∧ stonePotencyFrom 0 false () ∧
    FirstBeingIsInNoWayInPotencyReading (stonePotencyFrom 0) groundPriorStone)

/-- Formal facts, over every carrier.
1. The composition premise gives its restriction to act in being.
2. With `ActualityOnlyInsofarAsBeingReading` the restriction gives it back.
3. With `ActualityOnlyInsofarAsBeingReading`, `FirstBeingIsInSomeAct` gives
   that every first being is in act in being. -/
def Facts : Prop :=
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (esse : R) (Composite : B → Prop),
    ActAndPotencyMakeComposite InAct InPotency Composite →
    ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite) ∧
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (esse : R) (Composite : B → Prop),
    ActualityOnlyInsofarAsBeingReading InAct esse →
    ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite →
    ActAndPotencyMakeComposite InAct InPotency Composite) ∧
  (∀ (B R : Type) (InAct : B → R → Prop) (esse : R) (PriorSimply : B → B → Prop),
    ActualityOnlyInsofarAsBeingReading InAct esse →
    FirstBeingIsInSomeAct InAct PriorSimply →
    ∀ f, IsFirstBeing PriorSimply f → InAct f esse)

/-- The control certificate. -/
def Certificate : Prop :=
  HeavenlyFirst ∧ ContingentFirst ∧ RestrictedStrict ∧ IdleUncausedComposite ∧
    ThetaEightOmissions ∧ PlenitudeOmissions ∧ Facts

end Control

end TruthCore.Causality.ActPriorityThetaEight
