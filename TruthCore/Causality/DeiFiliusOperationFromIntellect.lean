module

public import TruthCore.Causality.DeiFiliusLivingNineScope
public import TruthCore.Causality.TermSenseForks3

/-! The nine's immanent operation from intellect, capacity and pure act

The root-reaching living route (results `bb1fc65d`, `78acb308`) rests on the bare
premise `NineOperate` (statement `8f93d9cc`): whatever has the nine has an
immanent operation (`Operates`, definition `7acc985a`). With the unmovedness of a
pure act, an immanent operation is close to the q.18 a.3 definiens of living, so
that premise carried most of the living conjunct's content. This module replaces
it by a derivation from three commitments that can be discussed apart from
living, and composes them with the pure act that the sixth of the nine already is:

* `IntellectIsCapacityToUnderstand`: whatever has intellect (HAS_INTELLECT_1) has
  the capacity to understand, `CapacityPotency CanBe x understanding` (POTENCY_3,
  `DEF-CAPACITY-TO-BE`, the `CanBe` of the *Metaphysics* Θ.6 analysis, whose own
  example is the knower able to contemplate);
* `UnderstandingCapacityExercisedOrInPotency`: whatever has that capacity is
  either actually understanding (`InAct x understanding`) or in potency to
  understanding (`InPotency x understanding`, the same potency predicate whose
  absence in every respect is pure act). Restricted to the one respect of
  understanding, an operation that remains in the agent; it says nothing about
  capacities whose exercise is an effect in another (see below);
* `ExercisedUnderstandingIsImmanentOperation`: whatever has the capacity to
  understand and is actually understanding has an immanent operation (q.18 a.3
  ad 1: understanding is an action that remains in the agent). `InAct` is the
  nine's shared act predicate, read formally or virtually (`DEF-UNIVERSALLY-PERFECT`,
  `DISAMB-IN-ACT`); the capacity condition does not exclude virtual act. On the
  inclusive reading this premise therefore also carries an explicit bridge: a
  being capable of understanding that is in act in understanding only virtually
  has an immanent operation. That bridge is part of the open premise.

From these, every pure act with intellect operates (`IntellectualPureActOperates`,
an intellect-restricted middle version between `STMT-PURE-ACT-OPERATES` and
`NineOperate`): the capacity is either exercised or a potency, and a pure act has
no potency, so it is exercised, and its exercise is an immanent operation.
`NineOperate` follows by projection (the nine include intellect and altogether
immutability, which is pure act).

No premise mentions life: neither `Lives` (LIVING_1), `LivesAt` (LIVING_2), nor
being unmoved. `Control.Controls` part 5 has all three premises and a being with
the nine that operates and does not live at any time, so this derivation reaches
operation only; living still needs the route's other steps
(`STMT-SELF-OPERATING-UNMOVED-LIVES`, the Prima Via motion premise, the sense
bridge).

Under the adopted sense of potency (`AdoptedPotency.InPotency`: capable and not
actually), the second premise is the instance of excluded middle for
`InAct x understanding` at a capable being (`exercisedOrInPotencyOfDecidable`
in the Solution proves it constructively from that instance). The derivation's
substantive inputs are then the first and third premises and the being's pure
actuality: in the adopted sense, a pure act is a being none of whose capacities
is unexercised.

Why only the respect of understanding. A general version ("every capacity is
exercised or a potency", over every respect) would make a pure act exercise
every capacity it has, including any capacity to produce an effect it does not
produce; the classical position (ST I q.25 a.5, God can do what he does not do;
attribution deferred, no claim on file) denies that such an unexercised power to
produce something puts its agent in potency. That is a reason inside the
framework not to use the general version; the restricted one does not face it.

Analyst formulations, attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusOperationFromIntellect

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Causality.TermSenseForks (CapacityPotency)
open TruthCore.Causality.DeiFiliusLivingNineScope
open TruthCore.Causality.DeiFiliusAttributeField (LivesSomeTime)

/-- Whatever has intellect (HAS_INTELLECT_1) has the capacity (POTENCY_3,
`CapacityPotency`) to be actually understanding. `understanding` is the respect
in which being in act is actually understanding something. Open premise,
analyst formulation. -/
def IntellectIsCapacityToUnderstand {Being Respect : Type} (HasIntellect : Being → Prop)
    (CanBe : Being → Respect → Prop) (understanding : Respect) : Prop :=
  ∀ x, HasIntellect x → CapacityPotency CanBe x understanding

/-- Whatever has the capacity to understand is actually understanding or is in
potency to understanding. Restricted to the respect of understanding. Open
premise, analyst formulation; classically equivalent to the right-to-left
direction of the Θ.6 analysis (`PotencyIsUnactualizedCapacityReading`) at this
one respect. -/
def UnderstandingCapacityExercisedOrInPotency {Being Respect : Type}
    (InAct InPotency CanBe : Being → Respect → Prop) (understanding : Respect) : Prop :=
  ∀ x, CapacityPotency CanBe x understanding →
    InAct x understanding ∨ InPotency x understanding

/-- Whatever has the capacity to understand and is actually understanding has an
immanent operation (`Operates`, definition `7acc985a`): understanding is an action
that remains in the agent (q.18 a.3 ad 1). Open premise, analyst formulation. -/
def ExercisedUnderstandingIsImmanentOperation {Being Respect : Type}
    (InAct CanBe : Being → Respect → Prop) (understanding : Respect)
    (Operates : Being → Prop) : Prop :=
  ∀ x, CapacityPotency CanBe x understanding → InAct x understanding → Operates x

/-- Intellect-restricted version of `STMT-PURE-ACT-OPERATES`: every pure act
with intellect has an immanent operation. Weaker than `PureActOperates`, stronger
than `NineOperate`. -/
def IntellectualPureActOperates {Being Respect : Type}
    (InPotency : Being → Respect → Prop) (HasIntellect Operates : Being → Prop) : Prop :=
  ∀ x, PureAct InPotency x → HasIntellect x → Operates x

namespace Control

open TruthCore.Causality.DeiFiliusLivingNineScope.Control

def none2 (_ : Bool) (_ : Unit) : Prop := False
def all2 (_ : Bool) (_ : Unit) : Prop := True
def neverAt (_ : Bool) (_ : Unit) : Prop := False

/-- The nine at a being of the two-being interpretation of
`DeiFiliusLivingNineScope.Control`, with the act predicate `A` supplied
(goodness holds everywhere) and intellect `I`. -/
abbrev NineWith (A : Bool → Unit → Prop) (I : Bool → Prop) (g : Bool) : Prop :=
  HasTheNine A inAct noPotency causes () isTrue no yes yes I yes g

/-- Checked interpretations on two beings (`Bool`), one respect (`()`, serving as
both esse and understanding) and one time, where nothing is in potency, nothing
is composite, only `true` is GOD_4 and everything causes everything:

1. without the first premise: nothing has the capacity to understand; the second
   and third premises hold, `true` has the nine, and nothing operates, so
   `NineOperate` fails;
2. without the second premise: everything is capable of understanding, nothing
   is in act; the first and third premises hold, `true` has the nine (perfection
   and supreme goodness hold vacuously, the latter with goodness supplied
   everywhere), and nothing operates;
3. without the third premise: everything is capable and in act; the first and
   second premises hold, `true` has the nine, and nothing operates;
4. nonvacuity: all three premises hold with only intellectual `true` operating,
   and `true` has the nine;
5. no life smuggled: in the interpretation of part 4, `true` has the nine and
   operates and lives at no time, and is not LIVING_1 on the primitives with no
   life;
6. strictness, middle against strong: on part 4, every pure act with intellect
   operates while `PureActOperates` fails (`false` is a pure act without intellect
   that does not operate);
7. strictness, nine against middle: with both beings intellectual and only `true`
   operating, `NineOperate` holds while `IntellectualPureActOperates` fails
   (`false` is an intellectual pure act that lacks the nine through uniqueness of
   GOD_4 and does not operate). -/
def Controls : Prop :=
  (UnderstandingCapacityExercisedOrInPotency inAct noPotency none2 () ∧
    ExercisedUnderstandingIsImmanentOperation inAct none2 () no ∧
    ¬ IntellectIsCapacityToUnderstand isTrue none2 () ∧
    Nine isTrue true ∧
    ¬ NineOperate inAct inAct noPotency causes () isTrue no yes yes isTrue yes no) ∧
  (IntellectIsCapacityToUnderstand isTrue all2 () ∧
    ExercisedUnderstandingIsImmanentOperation none2 all2 () no ∧
    ¬ UnderstandingCapacityExercisedOrInPotency none2 noPotency all2 () ∧
    NineWith none2 isTrue true ∧
    ¬ NineOperate none2 inAct noPotency causes () isTrue no yes yes isTrue yes no) ∧
  (IntellectIsCapacityToUnderstand isTrue all2 () ∧
    UnderstandingCapacityExercisedOrInPotency inAct noPotency all2 () ∧
    ¬ ExercisedUnderstandingIsImmanentOperation inAct all2 () no ∧
    Nine isTrue true ∧
    ¬ NineOperate inAct inAct noPotency causes () isTrue no yes yes isTrue yes no) ∧
  (IntellectIsCapacityToUnderstand isTrue onlyTrueAt () ∧
    UnderstandingCapacityExercisedOrInPotency inAct noPotency onlyTrueAt () ∧
    ExercisedUnderstandingIsImmanentOperation inAct onlyTrueAt () isTrue ∧
    Nine isTrue true) ∧
  (Nine isTrue true ∧ isTrue true ∧ ¬ LivesSomeTime neverAt true ∧
    ¬ (TruthCore.Causality.DeiFiliusLivingSelfOperation.Control.prims no).Lives true) ∧
  (IntellectualPureActOperates noPotency isTrue isTrue ∧
    ¬ TruthCore.Causality.SelfOperationLife.PureActOperates noPotency isTrue) ∧
  (NineOperate inAct inAct noPotency causes () isTrue no yes yes yes yes isTrue ∧
    ¬ IntellectualPureActOperates noPotency yes isTrue)

end Control
end TruthCore.Causality.DeiFiliusOperationFromIntellect
