module

public import TruthCore.Causality.TermSenseForks
public import TruthCore.Causality.GodMaximalCausal
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaGreatestDegree
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
public import TruthCore.Alternatives.ActPotencyRegress

/-! Sense forks, batch 3: "maxime ens" and "potency"

Analyst formulations, attribution deferred. Owner rules (#1233 B): every sense
is its own Lean declaration, one argument per sense, coverage and exclusivity
as explicit open premises, and every per-sense argument concludes an existing
root-route node or reaches one through a named bridge premise. Reuses the
generic coverage (`SensesCover`), exclusivity (`SenseUnique`) and uses-agree
vocabulary of `TermSenseForks` (DEF-ROUTE-SENSE-SELECTION).

* **maxime ens** (DISAMB-MAXIME-ENS). The quarta via's last step uses the
  superlative twice: something is maxime ens (existence use), and what is
  maxime in a genus causes all in the genus (causal use). The root-route node
  STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL reads the superlative as merely maximal.
  Senses, each its own declaration: MAXIMAL (`IsMaximalIn`, nothing is more a
  being), GREATEST_DEGREE (`GreatestDegreeBearer` at esse, a greatest
  represented degree, ties allowed) and STRICT (`StrictlyGreatestIn`, new:
  more a being than every other thing). Not senses of this use: Anselm's
  greatest conceivable being (a conceptual description no root statement
  uses), the calibration profile (bridge vocabulary between senses), and the
  maximum in an arbitrary perfection (the same `IsMaximalIn` at a general
  respect).
* **potency** (DISAMB-POTENCY). The prima via step to "nothing moves itself in
  the same respect" uses "in potency" twice: what is moved is in potency, and
  nothing is in act and in potency in the same respect. Senses: ADOPTED
  (`AdoptedPotency.InPotency`, capacity without act), INDEPENDENT (the
  primitive `InPotency` parameter, DEF-INDEPENDENT-POTENCY) and CAPACITY
  (`CapacityPotency`, new: capacity whether or not exercised). The Megarian
  thesis constrains CAPACITY's relation rather than giving a further reading,
  and receptive potency relates a principle to a received act, a different
  type. -/

@[expose] public section

namespace TruthCore.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae

/-! ## "maxime ens" -/

/-- MAXIME_3 (DEF-GREATEST-BEING-STRICT): `m` has `r` and is more `r` than
every other thing. The strict comparative clause is the one of
`QuartaViaStrictCausalTop`, without its maximality and causal conjuncts. -/
def StrictlyGreatestIn {Being Respect : Type} (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (r : Respect) (m : Being) : Prop :=
  InAct m r ∧ ∀ x, x ≠ m → MoreIn r m x

/-- The senses of the quarta via's superlative, in DISAMB-MAXIME-ENS's order of
the senses that are readings of the route's use: MAXIME_1 maximal
(DEF-MAXIME-ENS), MAXIME_2 greatest represented degree
(DEF-GREATEST-DEGREE-IN-A-PERFECTION at esse), MAXIME_3 strict supremacy
(DEF-GREATEST-BEING-STRICT). -/
inductive MaximeSense
  | maximal
  | greatestDegree
  | strict
  deriving DecidableEq

/-- The two uses of the superlative in the quarta via's last step. -/
inductive MaximeUse
  | existence
  | causal
  deriving DecidableEq

/-- The sense-indexed superlative of the optional summary; each constructor
unfolds to its sense's own declaration at esse. Per-sense statements never use
it. -/
def MaximeBy {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree) : MaximeSense → Being → Prop
  | .maximal => IsMaximalIn InAct MoreIn esse
  | .greatestDegree => GreatestDegreeBearer InAct esse value
  | .strict => StrictlyGreatestIn InAct MoreIn esse

/-- COVERAGE (STMT-MAXIME-SENSES-EXHAUSTIVE): each use of the superlative in the
quarta via's last step is read as maximal, greatest-degree or strictly greatest
in being, selected by the route's reading. OPEN frontier premise. -/
def MaximeSensesExhaustive {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree) (Select : MaximeSense → Prop)
    (use : MaximeUse → Being → Prop) : Prop :=
  SensesCover (MaximeBy InAct MoreIn esse value) Select use

/-- EXCLUSIVITY (STMT-MAXIME-SENSE-UNIQUE): the route's reading of the
superlative selects at most one sense. Not a disjointness claim. OPEN. -/
def MaximeSenseUnique (Select : MaximeSense → Prop) : Prop :=
  SenseUnique Select

/-- Something is maxime ens, the superlative in the route's reading of the
existence use. -/
def SomeMaximeInRouteSense {Being : Type} (use : MaximeUse → Being → Prop) : Prop :=
  ∃ m, use .existence m

/-- Whatever is maxime ens, in the route's reading of the causal use, causes
being in every other being. -/
def RouteMaximeCausesAllBeings {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (use : MaximeUse → Being → Prop) : Prop :=
  ∀ m, use .causal m → CausesAllInGenus InAct CausesIn esse m

/-- MAXIME_1: some being is maximal in being. -/
def SomeBeingMaximalInBeing {Being Respect : Type} (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∃ m, IsMaximalIn InAct MoreIn esse m

/-- MAXIME_2: some being has the greatest represented degree of being. -/
def SomeBeingGreatestInBeing {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (esse : Respect) (value : Being → Degree) : Prop :=
  ∃ m, GreatestDegreeBearer InAct esse value m

/-- MAXIME_3: some being is more a being than every other thing. -/
def SomeBeingStrictlyGreatestInBeing {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) : Prop :=
  ∃ m, StrictlyGreatestIn InAct MoreIn esse m

/-- MAXIME_3: whatever is more a being than every other thing causes being in
every other being. -/
def StrictlyGreatestInBeingCausesAllBeings {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ m, StrictlyGreatestIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m

/-- Sense bridge MAXIME_2 → MAXIME_1: a greatest-degree bearer of being is
maximal in being. OPEN analyst bridge. -/
def GreatestInBeingIsMaximal {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree) : Prop :=
  ∀ m, GreatestDegreeBearer InAct esse value m → IsMaximalIn InAct MoreIn esse m

/-- Sense bridge MAXIME_3 → MAXIME_1: what is more a being than every other
thing is maximal in being. OPEN analyst bridge. -/
def StrictlyGreatestInBeingIsMaximal {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) : Prop :=
  ∀ m, StrictlyGreatestIn InAct MoreIn esse m → IsMaximalIn InAct MoreIn esse m

/-- Comparison in being tracks represented degree: whatever is more a being
than `m` has being and a strictly higher degree than `m`. One direction of the
calibration of `MaximumDefinitionFork.StrictDegreeCalibration`, at esse and
without its frame. OPEN analyst premise. -/
def MoreInBeingTracksDegree {Being Respect Degree : Type} [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) (value : Being → Degree) : Prop :=
  ∀ y m, MoreIn esse y m → InAct y esse ∧ value m < value y

/-- MAXIME_1 → MAXIME_3 for the causal principle's antecedent: whatever is
MAXIMAL in being is STRICTLY greatest in being. OPEN analyst bridge (it is what
the strict reading of the causal principle needs to reach the MAXIMAL root
statement). -/
def MaximalInBeingIsStrictlyGreatest {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (esse : Respect) : Prop :=
  ∀ m, IsMaximalIn InAct MoreIn esse m → StrictlyGreatestIn InAct MoreIn esse m

/-- Any two distinct things are comparable in being: one is more a being than
the other. OPEN analyst premise; it ranges over all things, not only over
beings having esse. -/
def MoreInBeingConnected {Being Respect : Type}
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ x y, x ≠ y → MoreIn esse x y ∨ MoreIn esse y x

/-! ## "potency" -/

/-- POTENCY_3 (DEF-CAPACITY-TO-BE): capacity for `r`, whether or not
exercised. Its own declaration, so that CAPACITY statements mention neither
adopted nor independent potency. -/
def CapacityPotency {Being Respect : Type} (CanBe : Being → Respect → Prop)
    (x : Being) (r : Respect) : Prop :=
  CanBe x r

/-- The senses of "in potency" on the prima via step, in DISAMB-POTENCY's order
of the senses that are readings of the route's use: POTENCY_1 adopted
(DEF-POTENCY), POTENCY_2 independent primitive (DEF-INDEPENDENT-POTENCY),
POTENCY_3 capacity (DEF-CAPACITY-TO-BE). -/
inductive PotencySense
  | adopted
  | independent
  | capacity
  deriving DecidableEq

/-- The two uses of "in potency" in the step to no self-motion. -/
inductive PotencyUse
  | moved
  | nonSimultaneity
  deriving DecidableEq

/-- The sense-indexed potency predicate of the optional summary; each
constructor unfolds to its sense's own declaration. -/
def PotencyBy {Being Respect : Type} (InAct CanBe InPotency : Being → Respect → Prop) :
    PotencySense → Being → Respect → Prop
  | .adopted => AdoptedPotency.InPotency InAct CanBe
  | .independent => InPotency
  | .capacity => CapacityPotency CanBe

/-- COVERAGE (STMT-POTENCY-SENSES-EXHAUSTIVE): each use of "in potency" in the
prima via step is read as adopted potency, independent potency or capacity,
selected by the route's reading. OPEN frontier premise. -/
def PotencySensesExhaustive {Being Respect : Type}
    (InAct CanBe InPotency : Being → Respect → Prop) (Select : PotencySense → Prop)
    (use : PotencyUse → Being → Respect → Prop) : Prop :=
  SensesCover (PotencyBy InAct CanBe InPotency) Select use

/-- EXCLUSIVITY (STMT-POTENCY-SENSE-UNIQUE): the route's reading of "in
potency" selects at most one sense. Not a disjointness claim. OPEN. -/
def PotencySenseUnique (Select : PotencySense → Prop) : Prop :=
  SenseUnique Select

/-- POTENCY_1: whatever is moved in a respect is in adopted potency there. -/
def MovedOnlyAsInAdoptedPotency {Being Respect : Type}
    (MovedIn InAct CanBe : Being → Respect → Prop) : Prop :=
  MovedOnlyAsInPotencyReading MovedIn (AdoptedPotency.InPotency InAct CanBe)

/-- POTENCY_3: whatever is moved in a respect has the capacity for it. -/
def MovedOnlyAsCapable {Being Respect : Type}
    (MovedIn CanBe : Being → Respect → Prop) : Prop :=
  MovedOnlyAsInPotencyReading MovedIn (CapacityPotency CanBe)

/-- POTENCY_3: nothing is in act in a respect while having the capacity for it. -/
def NothingActualAndCapable {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  NotActAndPotencyInSameRespectReading InAct (CapacityPotency CanBe)

/-- The CAPACITY non-simultaneity fails. -/
def CapacityNonSimultaneityFails {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  ¬ NothingActualAndCapable InAct CanBe

/-- Some capacity is retained while exercised: something is in act in a respect
and has the capacity for it (the builder who is building, *Met.* Θ.3).
OPEN analyst premise. -/
def SomeCapacityExercised {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  ∃ x r, InAct x r ∧ CapacityPotency CanBe x r

/-- Something has some capacity. OPEN analyst premise. -/
def SomethingHasACapacity {Being Respect : Type} (CanBe : Being → Respect → Prop) : Prop :=
  ∃ x r, CanBe x r

/-! ## Controls -/

/-- Controls of batch 3. -/
def TermSenseForks3Controls : Prop :=
  -- maxime: coverage without exclusivity; the existence use is maximal, the
  -- causal use greatest-degree; two incomparable maximal beings, no greatest
  -- degree, nothing causes; both sense bridges hold
  (∃ (Degree : Type) (_ : Preorder Degree)
      (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (value : Bool → Degree)
      (Select : MaximeSense → Prop) (use : MaximeUse → Bool → Prop),
    MaximeSensesExhaustive InAct MoreIn () value Select use ∧ ¬ MaximeSenseUnique Select ∧
    SomeMaximeInRouteSense use ∧ RouteMaximeCausesAllBeings InAct CausesIn () use ∧
    GreatestInBeingIsMaximal InAct MoreIn () value ∧
    StrictlyGreatestInBeingIsMaximal InAct MoreIn () ∧
    ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn ()) ∧
  -- maxime: coverage fails (the existence use is no sense), the rest holds
  (∃ (Degree : Type) (_ : Preorder Degree)
      (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (value : Bool → Degree)
      (Select : MaximeSense → Prop) (use : MaximeUse → Bool → Prop),
    ¬ MaximeSensesExhaustive InAct MoreIn () value Select use ∧ MaximeSenseUnique Select ∧
    SomeMaximeInRouteSense use ∧ RouteMaximeCausesAllBeings InAct CausesIn () use ∧
    GreatestInBeingIsMaximal InAct MoreIn () value ∧
    StrictlyGreatestInBeingIsMaximal InAct MoreIn () ∧
    ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn ()) ∧
  -- maxime: nonvacuity of the joint theorem, with two beings
  (∃ (Degree : Type) (_ : Preorder Degree)
      (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (value : Bool → Degree)
      (Select : MaximeSense → Prop) (use : MaximeUse → Bool → Prop),
    MaximeSensesExhaustive InAct MoreIn () value Select use ∧ MaximeSenseUnique Select ∧
    SomeMaximeInRouteSense use ∧ RouteMaximeCausesAllBeings InAct CausesIn () use ∧
    GreatestInBeingIsMaximal InAct MoreIn () value ∧
    StrictlyGreatestInBeingIsMaximal InAct MoreIn () ∧
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn () ∧ (∃ x y : Bool, x ≠ y)) ∧
  -- maxime, GREATEST_DEGREE branch without its bridge: a greatest-degree bearer
  -- causes all, but something is more a being than it
  (∃ (Degree : Type) (_ : Preorder Degree)
      (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop) (value : Bool → Degree),
    SomeBeingGreatestInBeing InAct () value ∧
    GreatestDegreeCausesAllInGenusReading InAct CausesIn () value ∧
    ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn ()) ∧
  -- maxime, STRICT branch without its bridge: a strictly greatest being causes
  -- all, but is also exceeded
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop),
    SomeBeingStrictlyGreatestInBeing InAct MoreIn () ∧
    StrictlyGreatestInBeingCausesAllBeings InAct MoreIn CausesIn () ∧
    ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn ()) ∧
  -- maxime, causal principle read STRICTLY without its bridge: tied maxima, so
  -- the strict principle holds vacuously and the MAXIMAL root statement fails
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop),
    StrictlyGreatestInBeingCausesAllBeings InAct MoreIn CausesIn () ∧
    ¬ MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn ()) ∧
  -- maxime: tied maxima; MAXIME_1 existence holds, MAXIME_3 existence fails, and
  -- more-in is asymmetric
  (∃ (InAct : Bool → Unit → Prop) (MoreIn : Unit → Bool → Bool → Prop),
    TruthCore.Causality.GodMaximalCausal.MoreInIsAsymmetric MoreIn ∧
    SomeBeingMaximalInBeing InAct MoreIn () ∧
    ¬ SomeBeingStrictlyGreatestInBeing InAct MoreIn ()) ∧
  -- potency: coverage without exclusivity; the moved use is capacity, the
  -- non-simultaneity use adopted; something moves itself
  (∃ (InAct CanBe InPotency MovedIn : Unit → Unit → Prop)
      (MovesIn : Unit → Unit → Unit → Prop) (Select : PotencySense → Prop)
      (use : PotencyUse → Unit → Unit → Prop),
    PotencySensesExhaustive InAct CanBe InPotency Select use ∧ ¬ PotencySenseUnique Select ∧
    MovedOnlyAsInPotencyReading MovedIn (use .moved) ∧
    MovesOnlyAsInActReading MovesIn InAct ∧
    NotActAndPotencyInSameRespectReading InAct (use .nonSimultaneity) ∧
    ¬ NothingMovesItselfInSameRespectReading MovedIn MovesIn) ∧
  -- potency: coverage fails, the rest holds
  (∃ (InAct CanBe InPotency MovedIn : Unit → Unit → Prop)
      (MovesIn : Unit → Unit → Unit → Prop) (Select : PotencySense → Prop)
      (use : PotencyUse → Unit → Unit → Prop),
    ¬ PotencySensesExhaustive InAct CanBe InPotency Select use ∧ PotencySenseUnique Select ∧
    MovedOnlyAsInPotencyReading MovedIn (use .moved) ∧
    MovesOnlyAsInActReading MovesIn InAct ∧
    NotActAndPotencyInSameRespectReading InAct (use .nonSimultaneity) ∧
    ¬ NothingMovesItselfInSameRespectReading MovedIn MovesIn) ∧
  -- potency: nonvacuity of the joint theorem, with motion
  (∃ (InAct CanBe InPotency MovedIn : Bool → Unit → Prop)
      (MovesIn : Bool → Bool → Unit → Prop) (Select : PotencySense → Prop)
      (use : PotencyUse → Bool → Unit → Prop),
    PotencySensesExhaustive InAct CanBe InPotency Select use ∧ PotencySenseUnique Select ∧
    MovedOnlyAsInPotencyReading MovedIn (use .moved) ∧
    MovesOnlyAsInActReading MovesIn InAct ∧
    NotActAndPotencyInSameRespectReading InAct (use .nonSimultaneity) ∧
    NothingMovesItselfInSameRespectReading MovedIn MovesIn ∧
    (∃ y x r, MovesIn y x r)) ∧
  -- potency, ADOPTED branch: omitting the mover-in-act premise allows self-motion
  (∃ (InAct CanBe MovedIn : Unit → Unit → Prop) (MovesIn : Unit → Unit → Unit → Prop),
    MovedOnlyAsInAdoptedPotency MovedIn InAct CanBe ∧
    ¬ NothingMovesItselfInSameRespectReading MovedIn MovesIn) ∧
  -- potency, ADOPTED branch: omitting the adopted moved premise allows self-motion
  (∃ (InAct MovedIn : Unit → Unit → Prop) (MovesIn : Unit → Unit → Unit → Prop),
    MovesOnlyAsInActReading MovesIn InAct ∧
    ¬ NothingMovesItselfInSameRespectReading MovedIn MovesIn)

end TruthCore.Causality.TermSenseForks
