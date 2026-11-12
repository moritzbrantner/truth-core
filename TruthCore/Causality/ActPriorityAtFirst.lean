module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Causality.Round2PerfectionPrimacy

/-! Act priority where the routes use it: at a first being

`ActSimplyPriorToPotencyReading` (STMT-ACT-SIMPLY-PRIOR-TO-POTENCY) quantifies
over every being in potency in any respect. Its two consumers that the stage-two
routes cannot bypass, `ComponentFirstness.noComponentFirst` and
`FirstBeingNoPotency.firstBeingNoPotency`, apply it only to a first being
(nothing other than it is simply prior to it). This module states that weak
version, `FirstBeingActPriority`, and an independent way to it.

* `FirstBeingActPriority`: whatever first being is in potency in a respect is
  simply posterior to some being in act in that respect. The strong reading
  implies it (an instance); `Control.coldStone` makes the order strict.
* Given same-respect non-overlap, the weak version is equivalent to the q.3 a.1
  conclusion `FirstBeingIsInNoWayInPotencyReading` (`Facts`, items 2 and 3).
  Weakening act priority to the routes' use leaves no gap between premise and
  conclusion: what the routes need is that a first being is in no way in
  potency.
* `FirstBeingIsInSomeAct` and `ActAndPotencyMakeComposite` (open, analyst
  formulations, unattributed): every first being is in act in some respect,
  and whatever is in act in one respect and in potency in another is
  composite. With the q.3 a.7 reading that every composite has a cause of its
  being other than itself, the bridge that causing another's perfection is
  efficiently causing it, and the q.2 a.3 reading that an efficient cause is
  prior to its effect, they give the weak version, and directly the q.3 a.1
  conclusion. The proof applies each premise only at a supposed first being;
  three of them are stated universally, so first-being instances would
  suffice. No premise says that an idle potency of a being other than a first
  one has a prior being in act.

`Composite`, `CausesIn`, `InAct`, `InPotency` and `PriorSimply` are the
supplied parameters of the reused readings; nothing here defines them.
-/

@[expose] public section

namespace TruthCore.Causality.ActPriorityAtFirst

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.Round2PerfectionPrimacy (PerfectionCausingInAnotherIsEfficient)

/-- Weak version of act's simple priority, restricted to first beings (OPEN,
analyst formulation): whatever first being is in potency in a respect is
simply posterior to some being in act in that respect. Since nothing other than
a first being is simply prior to it, the witness is the first being itself: the
statement says that a first being's potencies are in act in the same respect,
and carries no priority over other beings. -/
def FirstBeingActPriority {B R : Type} (InAct InPotency : B → R → Prop)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ f, IsFirstBeing PriorSimply f → ∀ r, InPotency f r → ∃ y, InAct y r ∧ PriorSimply y f

/-- OPEN, analyst formulation, unattributed: whatever is in act in some respect
and in potency in some respect is composite. A being whose actual being leaves
a capacity unrealized has two principles, what it actually is and what it can
be but is not. ST I q.3 a.7 co., fourth reason, states the converse (every
composite has potency and act), not this direction. `InPotency` is the free
POTENCY_2 parameter, presupposing real passive potency; `Composite` is read in
the inclusive SIMPLE_4 sense, so that the q.3 a.7 cause premise covers
act-potency composition. The restriction to beings in
act in some respect keeps pure potency out: prime matter, in potency and in act
in no respect, is not composite, and would falsify the unrestricted
"whatever is in potency is composite" if it is counted among the beings. -/
def ActAndPotencyMakeComposite {B R : Type} (InAct InPotency : B → R → Prop)
    (Composite : B → Prop) : Prop :=
  ∀ x r s, InAct x s → InPotency x r → Composite x

/-- OPEN, analyst formulation, unattributed: every first being is in act in
some respect. Its denial is a first principle in act in nothing, the shape of
the potency-first cosmologies (Night, the seed) that ST I q.4 a.1 ad 2 answers. -/
def FirstBeingIsInSomeAct {B R : Type} (InAct : B → R → Prop)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ f, IsFirstBeing PriorSimply f → ∃ s, InAct f s

/-- Every being in potency in a respect has a distinct `G`-predecessor in act in
that respect. With `G := ActualConcreteGround m w` this is the commitment that
the strong reading carries on the routes that read simple priority as actual
concrete grounding (`STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`). -/
def PotencyHasDistinctPredecessorInAct {B R : Type} (InAct InPotency : B → R → Prop)
    (G : B → B → Prop) : Prop :=
  ∀ x r, InPotency x r → ∃ y, y ≠ x ∧ InAct y r ∧ G y x

namespace Control

/-! Two-being interpretations over `Bool` with two respects over `Bool`:
the being `true` is a ground, `false` a stone; the respect `true` is esse,
`false` heat. -/

/-- Everything is in act in esse; nothing is hot. -/
def esseAct (_ : Bool) (r : Bool) : Prop := r = true
/-- Nothing is in act in any respect. -/
def noAct (_ _ : Bool) : Prop := False
/-- The stone is in potency to heat. -/
def stonePotency (x r : Bool) : Prop := x = false ∧ r = false
/-- The ground is simply prior to the stone. -/
def groundPrior (y x : Bool) : Prop := y = true ∧ x = false
/-- The stone is composite. -/
def stoneComposite (x : Bool) : Prop := x = false
/-- The ground causes the stone's being. -/
def groundCauses (c x _ : Bool) : Prop := c = true ∧ x = false
/-- Nothing is simply prior to anything. -/
def noPrior (_ _ : Bool) : Prop := False
/-- Nothing causes anything. -/
def noCause (_ _ _ : Bool) : Prop := False
/-- Nothing is composite. -/
def noComposite (_ : Bool) : Prop := False

/-- Cold stone: the weak version, non-overlap, the four premises of the
composition route, an existing first being (`true`) and an existing potency
(the stone to heat) hold, while the strong reading fails: the stone has a
simply prior ground, but nothing is in act in heat. -/
def ColdStone : Prop :=
  FirstBeingActPriority esseAct stonePotency groundPrior ∧
  NotActAndPotencyInSameRespectReading esseAct stonePotency ∧
  FirstBeingIsInSomeAct esseAct groundPrior ∧
  ActAndPotencyMakeComposite esseAct stonePotency stoneComposite ∧
  CompositeHasAUnitingCauseReading stoneComposite groundCauses true ∧
  PerfectionCausingInAnotherIsEfficient groundCauses groundCauses ∧
  EfficientCauseIsPriorToEffectReading groundCauses groundPrior ∧
  IsFirstBeing groundPrior true ∧ stonePotency false false ∧
  ¬ ActSimplyPriorToPotencyReading esseAct stonePotency groundPrior

/-- Each composition-route premise is needed: dropping one leaves the other
four and non-overlap while the stone, first because nothing is prior to it,
is in potency to heat. (a) Without first-being act: nothing is in act (the
potency-first shape). (b) Without act-and-potency composition: the stone is in
act in esse, in potency to heat and simple. (c) Without composite-has-a-cause:
the stone is an uncaused composite. (d) Without efficient-cause priority: the
ground efficiently causes the composite stone, but nothing is simply prior.
(e) Without the cause-to-efficient-cause bridge: the ground causes the
composite stone, but not efficiently. -/
def CompositionOmissions : Prop :=
  (ActAndPotencyMakeComposite noAct stonePotency noComposite ∧
    CompositeHasAUnitingCauseReading noComposite noCause true ∧
    PerfectionCausingInAnotherIsEfficient noCause noCause ∧
    EfficientCauseIsPriorToEffectReading noCause noPrior ∧
    NotActAndPotencyInSameRespectReading noAct stonePotency ∧
    ¬ FirstBeingIsInSomeAct noAct noPrior ∧
    ¬ FirstBeingActPriority noAct stonePotency noPrior) ∧
  (FirstBeingIsInSomeAct esseAct noPrior ∧
    CompositeHasAUnitingCauseReading noComposite noCause true ∧
    PerfectionCausingInAnotherIsEfficient noCause noCause ∧
    EfficientCauseIsPriorToEffectReading noCause noPrior ∧
    NotActAndPotencyInSameRespectReading esseAct stonePotency ∧
    ¬ ActAndPotencyMakeComposite esseAct stonePotency noComposite ∧
    ¬ FirstBeingActPriority esseAct stonePotency noPrior) ∧
  (FirstBeingIsInSomeAct esseAct noPrior ∧
    ActAndPotencyMakeComposite esseAct stonePotency stoneComposite ∧
    PerfectionCausingInAnotherIsEfficient noCause noCause ∧
    EfficientCauseIsPriorToEffectReading noCause noPrior ∧
    NotActAndPotencyInSameRespectReading esseAct stonePotency ∧
    ¬ CompositeHasAUnitingCauseReading stoneComposite noCause true ∧
    ¬ FirstBeingActPriority esseAct stonePotency noPrior) ∧
  (FirstBeingIsInSomeAct esseAct noPrior ∧
    ActAndPotencyMakeComposite esseAct stonePotency stoneComposite ∧
    CompositeHasAUnitingCauseReading stoneComposite groundCauses true ∧
    PerfectionCausingInAnotherIsEfficient groundCauses groundCauses ∧
    NotActAndPotencyInSameRespectReading esseAct stonePotency ∧
    ¬ EfficientCauseIsPriorToEffectReading groundCauses noPrior ∧
    ¬ FirstBeingActPriority esseAct stonePotency noPrior) ∧
  (FirstBeingIsInSomeAct esseAct noPrior ∧
    ActAndPotencyMakeComposite esseAct stonePotency stoneComposite ∧
    CompositeHasAUnitingCauseReading stoneComposite groundCauses true ∧
    EfficientCauseIsPriorToEffectReading noCause noPrior ∧
    NotActAndPotencyInSameRespectReading esseAct stonePotency ∧
    ¬ PerfectionCausingInAnotherIsEfficient groundCauses noCause ∧
    ¬ FirstBeingActPriority esseAct stonePotency noPrior)

/-- Formal facts, over every carrier.
1. The strong reading implies the weak version.
2. The weak version and non-overlap give the q.3 a.1 conclusion.
3. The q.3 a.1 conclusion gives the weak version (no other premise).
4. The strong reading, non-overlap and a bridge from simple priority between
   distinct beings to `G` give every being in potency a distinct
   `G`-predecessor in act in that respect.
5. Non-overlap is needed in 2 (a lone being in act and potency in one respect,
   and first, satisfies the weak version). -/
def Facts : Prop :=
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (PriorSimply : B → B → Prop),
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
    FirstBeingActPriority InAct InPotency PriorSimply) ∧
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (PriorSimply : B → B → Prop),
    FirstBeingActPriority InAct InPotency PriorSimply →
    NotActAndPotencyInSameRespectReading InAct InPotency →
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply) ∧
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (PriorSimply : B → B → Prop),
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply →
    FirstBeingActPriority InAct InPotency PriorSimply) ∧
  (∀ (B R : Type) (InAct InPotency : B → R → Prop) (PriorSimply G : B → B → Prop),
    ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
    NotActAndPotencyInSameRespectReading InAct InPotency →
    (∀ y x, y ≠ x → PriorSimply y x → G y x) →
    PotencyHasDistinctPredecessorInAct InAct InPotency G) ∧
  (FirstBeingActPriority (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ => True) ∧
    ¬ FirstBeingIsInNoWayInPotencyReading (fun (_ : Unit) (_ : Unit) => True)
      (fun _ _ => True))

/-- The control certificate. -/
def Certificate : Prop := ColdStone ∧ CompositionOmissions ∧ Facts

end Control

end TruthCore.Causality.ActPriorityAtFirst
