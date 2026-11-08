module

public import TruthCore.Causality.TermSenseForks
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-! Sense forks, batch 4: "mutable / in potency in some way" and "God"

Analyst formulations, attribution deferred. Owner rules (#1233 B): every sense
is its own Lean declaration, one argument per sense, coverage and exclusivity
as explicit open premises, and every per-sense argument concludes an existing
root-route node or reaches one through a named bridge premise. Reuses the
generic coverage (`SensesCover`) and exclusivity (`SenseUnique`) vocabulary of
`TermSenseForks` (DEF-ROUTE-SENSE-SELECTION).

* **mutable** (DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER, with its duplicate
  DISAMB-MUTABILITY-CHANNEL). ST I q.9 a.2 says a thing is called mutable in
  two ways: through a potency in itself, and through a power in another (the
  creator's power to give or withhold its esse). The root argument
  IMMUTABLE-IS-PRIMITIVE-ETERNAL-FROM-TYPED-BOETHIAN uses "in potency in some
  respect" twice: what has succession in its life is in potency, and what
  begins or ceases to live is in potency. Senses, each its own declaration:
  IN_SUBJECT (`MutableInSubject`), THROUGH_ANOTHER (`MutableThroughAnother`,
  over the new typed power relation `PowerOver`) and IN_SOME_WAY
  (`MutableInSomeWay`, either channel: the negation of q.9 a.2's *omnino
  immutabile*).
* **God** (DISAMB-GOD). The designated root route uses "God" twice: the fully
  described principle is God (STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE),
  and whatever is God has the classical attributes
  (STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES). Senses of that use: NOMINAL
  (`NominalGod`, new: what the name signifies, q.13 a.8 ad 2 with the quarta
  via's cause of every perfection), SUMMA (the free `God` parameter of the
  older stage-1 routes), USAGE (`CalledGod`, new: a community applies the name
  to it, "et hoc dicimus Deum") and CLASSICAL (`Signature.IsGod`). Scott's and
  Gödel's `GodLike` are not readings of this use: they are world-indexed
  predicates over a positivity constant, a different type. -/

@[expose] public section

namespace TruthCore.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-! ## "mutable" -/

section Mutable

variable {Being Respect Time State : Type}

/-- MUTABLE_1, IN_SUBJECT (DEF-POTENCY): `x` is in potency in itself in some
respect, the `InPotency` that `PureAct` quantifies over. -/
def MutableInSubject (InPotency : Being → Respect → Prop) (x : Being) : Prop :=
  ∃ r, InPotency x r

/-- MUTABLE_2, THROUGH_ANOTHER (DEF-MUTABLE-THROUGH-ANOTHER, q.9 a.2): some
other being has the power to change `x` in some respect. `PowerOver y x r` is
the typed "power in another": `y` can change `x` in respect `r`, above all by
giving or withholding its esse. The relation is a framework input; it is not
assumed irreflexive (hence the distinctness clause), transitive or
well-founded, and it says nothing about potency in `x`. -/
def MutableThroughAnother (PowerOver : Being → Being → Respect → Prop) (x : Being) : Prop :=
  ∃ y r, y ≠ x ∧ PowerOver y x r

/-- MUTABLE_3, IN_SOME_WAY (DEF-MUTABLE-IN-SOME-WAY): `x` is mutable through a
potency in itself or through a power in another. Its negation is q.9 a.2's
*omnino immutabile*. Written out, so that it does not unfold to the other two
senses' declarations. -/
def MutableInSomeWay (InPotency : Being → Respect → Prop)
    (PowerOver : Being → Being → Respect → Prop) (x : Being) : Prop :=
  (∃ r, InPotency x r) ∨ (∃ y r, y ≠ x ∧ PowerOver y x r)

/-- The senses of "mutable / in potency in some way", in the order of
DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER's `sense_definition_ids`. -/
inductive MutabilitySense
  | inSubject
  | throughAnother
  | inSomeWay
  deriving DecidableEq

/-- The two uses of "in potency in some respect" in the root argument
IMMUTABLE-IS-PRIMITIVE-ETERNAL-FROM-TYPED-BOETHIAN. -/
inductive MutabilityUse
  | succession
  | boundary
  deriving DecidableEq

/-- The sense-indexed mutability predicate of the optional summary; each
constructor unfolds to its sense's own declaration. -/
def MutableBy (InPotency : Being → Respect → Prop)
    (PowerOver : Being → Being → Respect → Prop) : MutabilitySense → Being → Prop
  | .inSubject => MutableInSubject InPotency
  | .throughAnother => MutableThroughAnother PowerOver
  | .inSomeWay => MutableInSomeWay InPotency PowerOver

/-- COVERAGE (STMT-MUTABILITY-SENSES-EXHAUSTIVE): each use of "in potency in
some respect" in the eternity step is read as mutable in itself, through
another, or in some way, selected by the route's reading. OPEN. -/
def MutabilitySensesExhaustive (InPotency : Being → Respect → Prop)
    (PowerOver : Being → Being → Respect → Prop) (Select : MutabilitySense → Prop)
    (use : MutabilityUse → Being → Prop) : Prop :=
  SensesCover (MutableBy InPotency PowerOver) Select use

/-- EXCLUSIVITY (STMT-MUTABILITY-SENSE-UNIQUE): the route's reading selects at
most one sense. Not a disjointness claim: IN_SUBJECT implies IN_SOME_WAY. OPEN. -/
def MutabilitySenseUnique (Select : MutabilitySense → Prop) : Prop :=
  SenseUnique Select

/-- MUTABLE_2: whatever begins or ceases to live is mutable through another:
some other being has power over it. OPEN. -/
def LifeBoundaryRequiresPowerInAnother [LT Time]
    (PowerOver : Being → Being → Respect → Prop) (LivesAt : Being → Time → Prop) : Prop :=
  ∀ x, LifeBeginsOrEnds LivesAt x → MutableThroughAnother PowerOver x

/-- MUTABLE_3: whatever begins or ceases to live is mutable in some way, the
contrapositive of q.10 a.1 with *omnino immutabile* read as immutable through
both channels. OPEN. -/
def LifeBoundaryRequiresSomeMutability [LT Time] (InPotency : Being → Respect → Prop)
    (PowerOver : Being → Being → Respect → Prop) (LivesAt : Being → Time → Prop) : Prop :=
  ∀ x, LifeBeginsOrEnds LivesAt x → MutableInSomeWay InPotency PowerOver x

/-- Sense bridge THROUGH_ANOTHER → IN_SUBJECT: whatever another being has
power over is in potency in itself in some respect. OPEN analyst bridge; a
being with no potency in itself that depends on another (an emanated pure
intelligence) denies it. -/
def SubjectOfAnothersPowerHasPotency (InPotency : Being → Respect → Prop)
    (PowerOver : Being → Being → Respect → Prop) : Prop :=
  ∀ x, MutableThroughAnother PowerOver x → MutableInSubject InPotency x

/-- The route's succession use: whatever has succession in its life is mutable
in the route's reading of that use (q.9 a.1 for succession). -/
def RouteSuccessionIsMutability [LT Time] (LivesAt : Being → Time → Prop)
    (lifeStateAt : Being → Time → State) (use : MutabilityUse → Being → Prop) : Prop :=
  ∀ x, LifeHasSuccession LivesAt lifeStateAt x → use .succession x

/-- The route's boundary use: whatever begins or ceases to live is mutable in
the route's reading of that use (q.10 a.1, contraposed). -/
def RouteBoundaryIsMutability [LT Time] (LivesAt : Being → Time → Prop)
    (use : MutabilityUse → Being → Prop) : Prop :=
  ∀ x, LifeBeginsOrEnds LivesAt x → use .boundary x

/-- Whatever is immutable in the route's reading of the succession use has a
life without beginning, end or succession. -/
def RouteImmutableHasUnchangingLife [LT Time] (LivesAt : Being → Time → Prop)
    (lifeStateAt : Being → Time → State) (use : MutabilityUse → Being → Prop) : Prop :=
  ∀ x, ¬ use .succession x → Interminable LivesAt x ∧ TotaSimul LivesAt lifeStateAt x

end Mutable

/-! ## "God" -/

section God

variable {Being Respect Name : Type}

/-- GOD_1, NOMINAL (DEF-GOD-NOMINAL-Q13): `m` meets everything the name
signifies under the adopted fuller profile: the only being maximal in being
(above all), causing the being and every perfection of every other being
(principle of all) and entering into the composition of nothing (remote from
all). The antecedent of `GodNamesTheFullyDescribedPrinciple`, as a predicate. -/
def NominalGod (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (m : Being) : Prop :=
  IsMaximumIn InAct MoreIn esse m ∧ CausesAllInGenus InAct CausesIn esse m ∧
    CausesEveryPerfectionOfOthers InAct CausesIn m ∧ RemoteFromAll ComponentOf m ∧
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m)

/-- GOD_3, USAGE (DEF-GOD-WHAT-ALL-UNDERSTAND): a speech community applies the
name `godName` to `x` (*et hoc dicimus Deum*). `Calls n x` is usage, not a
claim about what `x` is. -/
def CalledGod (Calls : Name → Being → Prop) (godName : Name) (x : Being) : Prop :=
  Calls godName x

/-- The senses of "God" on the designated root route, in DISAMB-GOD's order of
the senses that are readings of that use: GOD_1 nominal, GOD_2 the Summa's
`God` parameter, GOD_3 usage, GOD_4 classical theism (`Signature.IsGod`). -/
inductive GodSense
  | nominal
  | summa
  | usage
  | classical
  deriving DecidableEq

/-- The two uses of "God" on the designated root route. -/
inductive GodUse
  | naming
  | attributes
  deriving DecidableEq

/-- The sense-indexed God predicate of the optional summary; each constructor
unfolds to its sense's declaration (the Summa's sense is the free parameter
`God` of the older stage-1 routes). -/
def GodBy (σ : Signature) (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop) (God : σ.Being → Prop)
    (Calls : Name → σ.Being → Prop) (godName : Name) : GodSense → σ.Being → Prop
  | .nominal => NominalGod InAct MoreIn CausesIn esse ComponentOf
  | .summa => God
  | .usage => CalledGod Calls godName
  | .classical => σ.IsGod

/-- COVERAGE (STMT-GOD-SENSES-EXHAUSTIVE): each use of "God" on the designated
root route is read in the nominal, Summa, usage or classical sense, selected by
the route's reading. OPEN. -/
def GodSensesExhaustive (σ : Signature) (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop) (God : σ.Being → Prop)
    (Calls : Name → σ.Being → Prop) (godName : Name) (Select : GodSense → Prop)
    (use : GodUse → σ.Being → Prop) : Prop :=
  SensesCover (GodBy σ InAct MoreIn CausesIn esse ComponentOf God Calls godName) Select use

/-- EXCLUSIVITY (STMT-GOD-SENSE-UNIQUE): the route's reading of "God" selects at
most one sense. Not a claim that the senses have disjoint extensions. OPEN. -/
def GodSenseUnique (Select : GodSense → Prop) : Prop :=
  SenseUnique Select

/-- The route's naming use: the fully described principle is God in the
route's reading. -/
def RouteNamesDescribedPrinciple (σ : Signature) (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop)
    (use : GodUse → σ.Being → Prop) : Prop :=
  ∀ m, NominalGod InAct MoreIn CausesIn esse ComponentOf m → use .naming m

/-- The route's attribute use: whatever is God in the route's reading has the
classical attributes. -/
def RouteGodHasClassicalAttributes (σ : Signature) (use : GodUse → σ.Being → Prop) : Prop :=
  ∀ g, use .attributes g → σ.HasClassicalAttributes g

/-- The fully described principle has the classical attributes. -/
def DescribedPrincipleHasClassicalAttributes (σ : Signature) (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop) : Prop :=
  ∀ m, NominalGod InAct MoreIn CausesIn esse ComponentOf m → σ.HasClassicalAttributes m

/-- GOD_1: the naming premise read NOMINALLY: whatever meets the full
description is God in what the name signifies. Analytic (proved from no
premise). A distinct declaration, so that it does not bind to
STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE. -/
def NominalGodNamesDescribedPrinciple (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (ComponentOf : Being → Being → Prop) : Prop :=
  GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf
    (NominalGod InAct MoreIn CausesIn esse ComponentOf)

/-- GOD_1: whatever is God NOMINALLY is maximal in being. Analytic. A distinct
declaration from `GodIsMaximalInBeing`, so that it does not bind to
STMT-GOD-IS-MAXIMAL-IN-BEING. -/
def NominalGodIsMaximalInBeing (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ g, NominalGod InAct MoreIn CausesIn esse ComponentOf g → IsMaximumIn InAct MoreIn esse g

/-- Sense bridge GOD_1 → GOD_4: whatever meets the full nominal description is
the God of classical theism. OPEN. -/
def NominalGodIsClassicalGod (σ : Signature) (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop) : Prop :=
  ∀ m, NominalGod InAct MoreIn CausesIn esse ComponentOf m → σ.IsGod m

/-- GOD_2 → GOD_4 bridge: whatever the Summa calls God (the `God` parameter of
the older stage-1 routes) is the God of classical theism. OPEN. -/
def SummaGodIsClassicalGod (σ : Signature) (God : σ.Being → Prop) : Prop :=
  ∀ g, God g → σ.IsGod g

/-- GOD_3: the naming premise read as USAGE: whatever meets the full
description is called God (*et hoc dicimus Deum*, extended to the fuller
profile). OPEN. -/
def DescribedPrincipleIsCalledGod (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (ComponentOf : Being → Being → Prop) (Calls : Name → Being → Prop)
    (godName : Name) : Prop :=
  GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf
    (CalledGod Calls godName)

/-- Sense bridge GOD_3 → GOD_4: whatever is called God is the God of classical
theism. OPEN; the "but is it God?" objection denies it. -/
def CalledGodIsClassicalGod (σ : Signature) (Calls : Name → σ.Being → Prop)
    (godName : Name) : Prop :=
  ∀ x, CalledGod Calls godName x → σ.IsGod x

end God

/-! ## Controls -/

/-- Controls of batch 4. -/
def TermSenseForks4Controls : Prop :=
  -- mutable: coverage without exclusivity; succession read IN_SUBJECT, boundary
  -- THROUGH_ANOTHER; a being with no potency in itself, in another's power,
  -- begins to live
  (∃ (InPotency : Bool → Unit → Prop) (PowerOver : Bool → Bool → Unit → Prop)
      (LivesAt : Bool → Nat → Prop) (lifeStateAt : Bool → Nat → Unit)
      (Select : MutabilitySense → Prop) (use : MutabilityUse → Bool → Prop),
    MutabilitySensesExhaustive InPotency PowerOver Select use ∧ ¬ MutabilitySenseUnique Select ∧
    (∀ x, LifeHasSuccession LivesAt lifeStateAt x → use .succession x) ∧
    (∀ x, LifeBeginsOrEnds LivesAt x → use .boundary x) ∧
    ¬ RouteImmutableHasUnchangingLife LivesAt lifeStateAt use) ∧
  -- mutable: nonvacuity of the joint theorem; something lives, unchanging
  (∃ (InPotency : Bool → Unit → Prop) (PowerOver : Bool → Bool → Unit → Prop)
      (LivesAt : Bool → Nat → Prop) (lifeStateAt : Bool → Nat → Unit)
      (Select : MutabilitySense → Prop) (use : MutabilityUse → Bool → Prop),
    MutabilitySensesExhaustive InPotency PowerOver Select use ∧ MutabilitySenseUnique Select ∧
    (∀ x, LifeHasSuccession LivesAt lifeStateAt x → use .succession x) ∧
    (∀ x, LifeBeginsOrEnds LivesAt x → use .boundary x) ∧
    RouteImmutableHasUnchangingLife LivesAt lifeStateAt use ∧ (∃ x t, LivesAt x t)) ∧
  -- mutable, THROUGH_ANOTHER and IN_SOME_WAY branches without the sense bridge:
  -- both boundary statements hold, the IN_SUBJECT root node fails
  (∃ (InPotency : Bool → Unit → Prop) (PowerOver : Bool → Bool → Unit → Prop)
      (LivesAt : Bool → Nat → Prop),
    LifeBoundaryRequiresPowerInAnother PowerOver LivesAt ∧
    LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt ∧
    ¬ LifeBoundaryRequiresPotencyReading InPotency LivesAt) ∧
  -- mutable, branches without their boundary premise: the bridge holds and the
  -- root node fails
  (∃ (InPotency : Unit → Unit → Prop) (PowerOver : Unit → Unit → Unit → Prop)
      (LivesAt : Unit → Nat → Prop),
    SubjectOfAnothersPowerHasPotency InPotency PowerOver ∧
    ¬ LifeBoundaryRequiresPotencyReading InPotency LivesAt) ∧
  -- God: coverage without exclusivity; naming read NOMINAL, attributes
  -- CLASSICAL; the fully described principle lacks the attributes
  (∃ (σ : Signature) (InAct : σ.Being → Unit → Prop) (MoreIn : Unit → σ.Being → σ.Being → Prop)
      (CausesIn : σ.Being → σ.Being → Unit → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
      (God : σ.Being → Prop) (Calls : Unit → σ.Being → Prop)
      (Select : GodSense → Prop) (use : GodUse → σ.Being → Prop),
    GodSensesExhaustive σ InAct MoreIn CausesIn () ComponentOf God Calls () Select use ∧
    ¬ GodSenseUnique Select ∧
    RouteNamesDescribedPrinciple σ InAct MoreIn CausesIn () ComponentOf use ∧
    RouteGodHasClassicalAttributes σ use ∧
    ¬ DescribedPrincipleHasClassicalAttributes σ InAct MoreIn CausesIn () ComponentOf) ∧
  -- God: nonvacuity of the joint theorem, with a described principle
  (∃ (σ : Signature) (InAct : σ.Being → Unit → Prop) (MoreIn : Unit → σ.Being → σ.Being → Prop)
      (CausesIn : σ.Being → σ.Being → Unit → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
      (God : σ.Being → Prop) (Calls : Unit → σ.Being → Prop)
      (Select : GodSense → Prop) (use : GodUse → σ.Being → Prop),
    GodSensesExhaustive σ InAct MoreIn CausesIn () ComponentOf God Calls () Select use ∧
    GodSenseUnique Select ∧
    RouteNamesDescribedPrinciple σ InAct MoreIn CausesIn () ComponentOf use ∧
    RouteGodHasClassicalAttributes σ use ∧
    DescribedPrincipleHasClassicalAttributes σ InAct MoreIn CausesIn () ComponentOf ∧
    (∃ m, NominalGod InAct MoreIn CausesIn () ComponentOf m)) ∧
  -- God, NOMINAL / SUMMA / USAGE branches without their bridges: the nominal
  -- naming (analytic), the Summa naming and the usage naming hold, a described
  -- principle exists, and the CLASSICAL root premise fails
  (∃ (σ : Signature) (InAct : σ.Being → Unit → Prop) (MoreIn : Unit → σ.Being → σ.Being → Prop)
      (CausesIn : σ.Being → σ.Being → Unit → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
      (God : σ.Being → Prop) (Calls : Unit → σ.Being → Prop),
    NominalGodNamesDescribedPrinciple InAct MoreIn CausesIn () ComponentOf ∧
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn () God ∧
    DescribedPrincipleIsCalledGod InAct MoreIn CausesIn () ComponentOf Calls () ∧
    (∃ m, NominalGod InAct MoreIn CausesIn () ComponentOf m) ∧
    ¬ GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn () ComponentOf σ.IsGod) ∧
  -- God, USAGE branch without its naming premise: the bridge holds, nothing is
  -- called God, and the root premise fails
  (∃ (σ : Signature) (InAct : σ.Being → Unit → Prop) (MoreIn : Unit → σ.Being → σ.Being → Prop)
      (CausesIn : σ.Being → σ.Being → Unit → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
      (Calls : Unit → σ.Being → Prop),
    CalledGodIsClassicalGod σ Calls () ∧
    ¬ GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn () ComponentOf σ.IsGod) ∧
  -- stage 1 from the quarta via's conclusion, that conclusion omitted: every
  -- other premise except excluded middle holds and nothing is God
  (∃ (InAct : Unit → Unit → Prop) (MoreIn : Unit → Unit → Unit → Prop)
      (CausesIn : Unit → Unit → Unit → Prop) (ComponentOf PriorSimply : Unit → Unit → Prop)
      (IsGod : Unit → Prop),
    ¬ MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn () ∧
    ActualityOnlyInsofarAsBeingReading InAct () ∧
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
    CauseOfBeingCausesEveryPerfection InAct CausesIn () ∧
    NoComponentIsFirstBeingReading ComponentOf PriorSimply ∧
    MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply ∧
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn () ComponentOf IsGod ∧
    ¬ GodExists IsGod)

end TruthCore.Causality.TermSenseForks
