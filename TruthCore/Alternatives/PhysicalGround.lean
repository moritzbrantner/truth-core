import TruthCore.Alternatives.MindPhysicalism
import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Causality.RootMultiplication
import TruthCore.Explanation.ExplanatorySymmetry
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2

/-!
# A necessary physical ground, tested on the standards of a classical ground (#468)

Which existing commitments separate a necessary impersonal physical ground from a
classical ground, and what each must give up. No declaration here says that either
exists, that either is metaphysically possible, or that any premise is true. Models
are finite analyst-built interpretations and may carry inert rows. Names such as
`rival` and `classical` are comparison labels for tables. See
`docs/notes/physical-ground-468.md` for readings, examples and rival accounts.
-/
namespace TruthCore.Alternatives.PhysicalGround

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.HistorySelection
open TruthCore.Logic
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers (Capacity)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt Ontic)
open TruthCore.Causality.NecessarilyUnderived (NecessarilyUnderived NoExistingSupportAt)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers (existsAt response)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (alternatingFrame alternatingExists)

namespace MP
export TruthCore.Alternatives.MindPhysicalism (Frame Completeness CausalInfluence
  EachCauseNotAllOverdetermined)
end MP

/-! ## Containment of an effect's perfections in its cause -/

/-- `Formal x r`: `x` has `r` in its own kind. `Virtual x r`: `x` has the power to
produce `r` without having `r` in its own kind. `Composite` is the Stage 2 parameter.
Nothing relates the two modes. -/
structure Table (B R : Type) where
  Formal : B → R → Prop
  Virtual : B → R → Prop
  CausesIn : B → B → R → Prop
  Composite : B → Prop
  esse : R

variable {B R : Type}

/-- The abstract `InAct` of DISAMB-IN-ACT, fixed by a classification: respects in `P`
count only formally, and all others formally or virtually. -/
def InActUnder (t : Table B R) (P : R → Prop) (x : B) (r : R) : Prop :=
  t.Formal x r ∨ (¬ P r ∧ t.Virtual x r)

/-- ST I q.4 a.2 (`PerfectionsOfEffectPreexistInCauseReading`) under that fixing. -/
def Contains (t : Table B R) (P : R → Prop) : Prop :=
  PerfectionsOfEffectPreexistInCauseReading (InActUnder t P) t.CausesIn t.esse

/-- A classification that does not consult the candidate: something other than `g`
has `r` formally and is not composite. Open and unattributed as a criterion of what
must be had formally. It uses only structure, and `g`'s own row cannot satisfy it. -/
def IndependentlyPure (t : Table B R) (g : B) (r : R) : Prop :=
  ∃ x, x ≠ g ∧ ¬ t.Composite x ∧ t.Formal x r

/-! ## The route from a maximum to intellect -/

/-- The Stage 2 parameters of `godHasIntellect` and `godHasWill`. -/
structure Route (B R P : Type) where
  MatterForm : B → Prop
  Composite : B → Prop
  HasIntellect : B → Prop
  HasWill : B → Prop
  ComponentOf : B → B → Prop
  PriorSimply : B → B → Prop
  essenceOf : B → P
  esseOf : B → P
  InAct : B → R → Prop
  MoreIn : R → B → B → Prop
  CausesIn : B → B → R → Prop
  esse : R

/-- The five premises from which a maximum is altogether immaterial. -/
structure Route.Structural {P : Type} (m : Route B R P) : Prop where
  uniting : CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse
  causeMore : CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn
  kinds : MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite
    m.essenceOf m.esseOf
  noComponent : NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply
  firstBeing : MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply

/-- `g` is a maximum of the route. -/
def Route.Maximum {P : Type} (m : Route B R P) (g : B) : Prop :=
  IsMaximumIn m.InAct m.MoreIn m.esse g

/-- ST I q.14 a.1 at the route's parameters. -/
def Route.Immaterial {P : Type} (m : Route B R P) : Prop :=
  ImmaterialIsIntellectualReading m.MatterForm m.HasIntellect m.ComponentOf

/-! ## Physical occurrences and their bearers -/

/-- A #419 frame whose occurrences have bearers. -/
structure Bearing (Occ Kind B : Type) where
  frame : MP.Frame Occ Kind
  bearer : Occ → B
  Composite : B → Prop

/-- Open and unattributed: the bearer of a physical occurrence is composite. This is one
sense of "physical" (DISAMB-PHYSICAL-GROUND); it is not Papineau's sense. -/
def PhysicalBearersComposite {Occ Kind : Type} (c : Bearing Occ Kind B) : Prop :=
  ∀ e, c.frame.Physical e → c.Composite (c.bearer e)

/-- Open and unattributed: a realizer has the bearer of what it realizes. -/
def RealizerSameBearer {Occ Kind : Type} (c : Bearing Occ Kind B) : Prop :=
  ∀ e r, c.frame.RealizedBy e r → c.bearer r = c.bearer e

/-! ## Intrinsic state of a ground -/

variable {W F : Type}

/-- A ground's intrinsic state at each world, with a fact for each state value. -/
structure StateFacts (X : Frame W B F) (S : Type) where
  state : W → S
  fact : S → F
  holds_fact : ∀ v s, X.arena.holds v (fact s) ↔ state v = s

/-! ## A conceivability test -/

/-- Open and unattributed: a being whose absence can be conceived does not exist necessarily.
Hume's *Dialogues* IX is a source lead with no pinned passage in the corpus, so nothing is
attributed to it here. -/
def ConceivabilityExcludesNecessity (Conceivable Necessary : B → Prop) : Prop :=
  ∀ x, Conceivable x → ¬ Necessary x

/-- Open and unattributed: if the absence of the material world can be conceived, so can the
absence of the deity. A parity conditional, not a claim about any source. -/
def TestExtendsEqually (Conceivable : B → Prop) (matter deity : B) : Prop :=
  Conceivable matter → Conceivable deity

/-! ## What necessity gives and does not -/

/-- Necessarily something exists: each accessible world has an existent. This is `□∃`, which
does not give one being in all of them. -/
def SomethingNecessarily {W B : Type} (m : Ontic W B) (a : W) : Prop :=
  ∀ v, m.frame.access a v → ∃ x, m.ExistsAt v x

/-- The #435 capacity model as an `Ontic`: `false` exists at both worlds and `true` only at `true`. -/
def powers : Ontic Bool Bool where
  frame := alternatingFrame
  ExistsAt := fun w x => existsAt x w
  Causes := fun _ _ _ => False

/-- A route's esse-causation read as direct existential support. An analyst identification,
for these tables only: DISAMB-EXISTENCE-ESSE-SUPPORT keeps the relations distinct in general. -/
def Route.supports {P : Type} (m : Route Bool R P) : Bool → Bool → Bool → Prop :=
  fun _ x y => m.CausesIn x y m.esse

/-- What the rival and the classical ground share, at the actual world `false`: the root exists,
exists necessarily, has no existing supporter at any world, has a capacity under the #435
response at every world, and is the esse-cause of the other being, which is contingent. No
attribute of the root is mentioned. -/
def Signature {P : Type} (m : Route Bool R P) : Prop :=
  powers.ExistsAt false false ∧ NecessaryAt powers false false ∧
  (∀ w, NoExistingSupportAt powers m.supports w false) ∧
  NecessarilyUnderived powers m.supports false ∧
  (∀ w, Capacity alternatingFrame existsAt response false w) ∧
  m.CausesIn false true m.esse ∧
  ContingentAt powers true true

/-- Open and unattributed: the marks of a choice at a world need a base reason borne by something
with the flag. The bridge a selection argument for will would need. -/
def MarksRequirePerson {W B F : Type} (X : Frame W B F) (base O : F → Prop) (a : W)
    (personal : B → Prop) : Prop :=
  Marks X base O a → PersonalStop X base personal

/-- One bearer table, with `false` existing at world `false` only. With `narrow` each world accesses
only itself; otherwise every world accesses both. -/
def onlyActual (narrow : Bool) : Ontic Bool Bool where
  frame := ⟨fun w v => narrow = false ∨ (w = v)⟩
  ExistsAt := fun w x => w = false ∧ x = false
  Causes := fun _ _ _ => False

/-- Each world has its own bearer: necessarily something, and nothing necessarily. -/
def rotating : Ontic Bool Bool where
  frame := alternatingFrame
  ExistsAt := fun w x => alternatingExists x w
  Causes := fun _ _ _ => False

/-! ## Models -/

/-- A ground, an embodied mind, a body and two optional rows. -/
inductive Node where
  | ground | mind | body | simpleMind | simpleBody
  deriving DecidableEq

/-- The respects compared. -/
inductive Perf where
  | esse | mental | bodily
  deriving DecidableEq

/-- `true` makes the ground have the respect formally. The optional rows have respects only
when switched on, and they are not composite: in a table with the switch off the row is
inert. The ground causes the esse of `mind` and `body`, and of a row only if it is on.
The ground has every respect virtually. The ground is composite exactly when formally
bodily. -/
def table (groundMental groundBodily simpleMind simpleBody : Bool) : Table Node Perf where
  Formal
    | .ground, .esse => True
    | .ground, .mental => groundMental = true
    | .ground, .bodily => groundBodily = true
    | .mind, .esse => True
    | .mind, .mental => True
    | .mind, .bodily => True
    | .body, .esse => True
    | .body, .mental => False
    | .body, .bodily => True
    | .simpleMind, .esse => simpleMind = true
    | .simpleMind, .mental => simpleMind = true
    | .simpleMind, .bodily => False
    | .simpleBody, .esse => simpleBody = true
    | .simpleBody, .mental => False
    | .simpleBody, .bodily => simpleBody = true
  Virtual
    | .ground, _ => True
    | _, _ => False
  CausesIn
    | .ground, .mind, .esse => True
    | .ground, .body, .esse => True
    | .ground, .simpleMind, .esse => simpleMind = true
    | .ground, .simpleBody, .esse => simpleBody = true
    | _, _, _ => False
  Composite
    | .ground => groundBodily = true
    | .mind => True
    | .body => True
    | .simpleMind => False
    | .simpleBody => False
  esse := .esse

/-- The formally bodily, not formally mental ground. -/
abbrev rival (a b : Bool) : Table Node Perf := table false true a b
/-- The formally mental, not formally bodily ground. -/
abbrev classical (a b : Bool) : Table Node Perf := table true false a b

/-- Respects counted only formally. -/
def onlyEsse : Perf → Prop := (· = .esse)
/-- The classification favouring a formally mental ground. -/
def withMental : Perf → Prop := fun r => r = .esse ∨ r = .mental
/-- The classification favouring a formally bodily ground. -/
def withBodily : Perf → Prop := fun r => r = .esse ∨ r = .bodily
/-- Every respect counted only formally. -/
def everyRespect : Perf → Prop := fun _ => True

/-- Route parameters on the root `false` and one other being `true`, the bearer and the
recipient of the #435 capacity model. The arguments, in order: is matter-form
at root and other; is composite at root and other; the root has intellect; the root is a
component of the other; `CausesIn c x` on the two cross pairs (other causes root, root causes
other); `MoreIn` on the two cross pairs; other is prior to root. Essence and esse are one. -/
def route2 (mfR mfO cpR cpO intR compR causesOR causesRO moreOR moreRO priorOR : Prop) :
    Route Bool Unit Unit where
  MatterForm | false => mfR | true => mfO
  Composite | false => cpR | true => cpO
  HasIntellect | false => intR | true => False
  HasWill | false => intR | true => False
  ComponentOf
    | false, true => compR
    | _, _ => False
  PriorSimply
    | true, false => priorOR
    | _, _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  InAct := fun _ _ => True
  MoreIn
    | _, true, false => moreOR
    | _, false, true => moreRO
    | _, _, _ => False
  CausesIn
    | true, false, _ => causesOR
    | false, true, _ => causesRO
    | _, _, _ => False
  esse := ()

/-- An endless scale: each number is matter-form, composite, caused by its successor and less
than it. No number is a maximum. -/
def endless : Route Nat Unit Unit where
  MatterForm := fun _ => True
  Composite := fun _ => True
  HasIntellect := fun _ => False
  HasWill := fun _ => False
  ComponentOf := fun _ _ => False
  PriorSimply := fun _ _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  InAct := fun _ _ => True
  MoreIn := fun _ y x => y = x + 1
  CausesIn := fun y x _ => y = x + 1
  esse := ()

/-- Rung 0. A root in the signature that is no maximum. It is a component of the other being,
which is simply prior to it, so ST I q.14 a.1 does not apply to it. -/
abbrev noMaximum : Route Bool Unit Unit := route2 False True False True False True False True True True True
/-- Rung 1. A maximum in the signature that is matter-form and composite with no uniting cause. -/
abbrev compositeRoot : Route Bool Unit Unit := route2 True True True True False False False True False True False
/-- Rung 2. A maximum in the signature that is altogether immaterial, with no intellect. -/
abbrev simpleImpersonal : Route Bool Unit Unit := route2 False True False True False False False True False True False
/-- Rung 3. As rung 4, with no will. -/
abbrev willless : Route Bool Unit Unit :=
  { route2 False True False True True False False True False True False with HasWill := fun _ => False }
/-- Rung 4. The positive route: a maximum with intellect and will. -/
abbrev classicalRoute : Route Bool Unit Unit := route2 False True False True True False False True False True False

/-- `ground` and `law` with `Capacity` read at their own existence predicates. -/
abbrev exOf {W B F : Type} (A : Arena W B F) : B → W → Prop := fun x w => A.ontic.ExistsAt w x

/-! ## Certificates -/

/-- Conditional consequences. Each clause assumes what it states and establishes none of it.

* Containment: under a classification, the esse-cause of a thing with a classified respect
  has that respect formally. The second clause is the first at `IndependentlyPure`.
* Route: `Structural` and a maximum give altogether immaterial; ST I q.14 a.1 gives intellect
  of that maximum, and ST I q.19 a.1 gives will.
* Bearers: with excluded middle and Papineau's three premises (the third distributive), an
  occurrence of the target kind on a noncomposite bearer is inconsistent with composite
  physical bearers and same-bearer realizers.
* State: worlds that swap an outcome, with base-fixed favouring and net selection at both, and
  a base of state facts, differ in state. A state that differs at an accessible world is a
  contingent fact. A reason-closed founded account of a contingent state fact does not have
  all its reasons contingent.
* Conceivability: the test with its extension to the deity excludes both, given the premise
  for the material world.
* Necessity: a necessary being gives necessarily something. -/
def Core : Prop :=
  (∀ (B R : Type) (t : Table B R) (P : R → Prop) (g x : B) (r : R),
    Contains t P → P r → t.CausesIn g x t.esse → t.Formal x r → t.Formal g r) ∧
  (∀ (B R : Type) (t : Table B R) (g x : B) (r : R),
    Contains t (IndependentlyPure t g) → IndependentlyPure t g r →
    t.CausesIn g x t.esse → t.Formal x r → t.Formal g r) ∧
  (∀ (B R P : Type) (m : Route B R P) (g : B), m.Structural → m.Maximum g →
    ¬ m.Composite g ∧ ¬ m.MatterForm g ∧ ∀ y, ¬ m.ComponentOf g y) ∧
  (∀ (B R P : Type) (m : Route B R P) (g : B), m.Structural → m.Maximum g → m.Immaterial →
    m.HasIntellect g) ∧
  (∀ (B R P : Type) (m : Route B R P) (g : B), m.Structural → m.Maximum g → m.Immaterial →
    WillFollowsIntellectReading m.HasIntellect m.HasWill → m.HasWill g) ∧
  (∀ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), ExcludedMiddle →
    MP.Completeness c.frame → MP.CausalInfluence c.frame →
    MP.EachCauseNotAllOverdetermined c.frame → c.frame.Mental e → ¬ c.Composite (c.bearer e) →
    PhysicalBearersComposite c → RealizerSameBearer c → False) ∧
  (∀ (W B F S : Type) (X : Frame W B F) (sf : StateFacts X S) (base O : F → Prop) (a v : W) (f : F),
    (∀ r, base r → ∃ s, r = sf.fact s) → BaseFixed X base →
    SelectedAt X base O a → SelectedAt X base O v →
    ExhaustiveAt X.arena O v → ExclusiveAt X.arena O a →
    O f → X.arena.holds a f → ¬ X.arena.holds v f → sf.state a ≠ sf.state v) ∧
  (∀ (W B F S : Type) (X : Frame W B F) (sf : StateFacts X S) (a v : W),
    Access X.arena a v → sf.state v ≠ sf.state a → Contingent X.arena a (sf.fact (sf.state a))) ∧
  (∀ (W B F S : Type) (X : Frame W B F) (sf : StateFacts X S) (a : W) (A : F → Prop),
    ReasonClosed X.arena a A (sf.fact (sf.state a)) →
    Contingent X.arena a (sf.fact (sf.state a)) → Founded X.arena a A →
    ¬ AllReasonsVary X.arena a A) ∧
  (∀ (B : Type) (Conceivable Necessary : B → Prop) (matter deity : B),
    ConceivabilityExcludesNecessity Conceivable Necessary →
    TestExtendsEqually Conceivable matter deity → Conceivable matter →
    ¬ Necessary matter ∧ ¬ Necessary deity) ∧
  (∀ (W B : Type) (m : Ontic W B) (a : W) (g : B), NecessaryAt m a g → SomethingNecessarily m a)

/-- Verdicts on named analyst-built models. No model is shown possible.

* Containment: every table below has one causal table for its switches. Counting every respect
  formally excludes both grounds; counting only esse keeps both; `withMental` and `withBodily`
  each keep exactly one, oppositely. Under `IndependentlyPure`, with both optional rows off both
  are kept, with only the simple mind on only the mental ground is kept, with only the simple
  body on only the bodily ground is kept, and with both on neither is.
* Route: on the root `false`, each conjunct below keeps the other members of the bundle {five structural
  premises, maximum, ST I q.14 a.1, no intellect at the maximum} and refutes one. The first
  conjunct refutes the last member and also has will.
* Bearers: the bundle of `Core`'s bearer clause with excluded middle assumed elsewhere; each
  witness keeps the other members and refutes one, except excluded middle.
* State: `varying` with state facts differs in state, has net selection at `0` and `1`, a
  contingent state fact, and no reason-closed account of the target. `oneWay` has one state, net
  selection at `0`, and not at `1`.
* Capacity: `ground` has a necessary being with a capacity under a supplied response; `law` has
  no necessary being and no capacity under any response. They agree on net selection under one
  favouring.
* The #697 part-free model's rival, and a conceivability control.
* Ladder: five routes on one carrier share `Signature`, so one necessity profile and one causal
  row from the root. Each keeps the premises below its rung and drops one premise: no maximum with
  the structural premises and ST I q.14 a.1; a composite maximum without the uniting premise and
  with no cause of its own; an immaterial maximum without q.14 a.1; a maximum with intellect
  without q.19 a.1; and the positive route with neither dropped.
* Coverage, with no attribute row consulted. Existence of something: `powers` has it, and the root
  of `ground` has no reason for its existence. `rotating` has it with no necessary being, and `law`
  lacks it. Contingency: `ground` has a nonnecessitating reason for its contingent target; `idle`
  has a necessary being and no reason for the target. Modal scope: one bearer table is necessary
  on a narrow frame and not on a wide one. Why this world: `acting` has the marks of a choice under
  both flags, and `MarksRequirePerson` holds at the true flag and fails at the false one. -/
def Verdicts : Prop :=
  -- containment
  ((rival false false).CausesIn = (classical false false).CausesIn ∧
    (rival true false).CausesIn = (classical true false).CausesIn ∧
    (rival false true).CausesIn = (classical false true).CausesIn) ∧
  (¬ Contains (rival false false) everyRespect ∧ ¬ Contains (classical false false) everyRespect) ∧
  (Contains (rival false false) onlyEsse ∧ Contains (classical false false) onlyEsse) ∧
  (Contains (classical false false) withMental ∧ ¬ Contains (rival false false) withMental) ∧
  (Contains (rival false false) withBodily ∧ ¬ Contains (classical false false) withBodily) ∧
  (Contains (rival false false) (IndependentlyPure (rival false false) .ground) ∧
    Contains (classical false false) (IndependentlyPure (classical false false) .ground)) ∧
  (Contains (classical true false) (IndependentlyPure (classical true false) .ground) ∧
    ¬ Contains (rival true false) (IndependentlyPure (rival true false) .ground)) ∧
  (Contains (rival false true) (IndependentlyPure (rival false true) .ground) ∧
    ¬ Contains (classical false true) (IndependentlyPure (classical false true) .ground)) ∧
  (¬ Contains (rival true true) (IndependentlyPure (rival true true) .ground) ∧
    ¬ Contains (classical true true) (IndependentlyPure (classical true true) .ground)) ∧
  -- route: positive, then one deletion per member
  (let m := route2 False True False True True False False True False True False;
    m.Structural ∧ m.Maximum false ∧ m.Immaterial ∧ m.HasIntellect false ∧
    WillFollowsIntellectReading m.HasIntellect m.HasWill ∧ m.HasWill false) ∧
  (let m := route2 True True True True False False False True False True False;
    ¬ CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
    CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
    MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
    NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
    MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
    m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (let m := route2 True True True True False False True True False False False;
    CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
    ¬ CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
    MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
    NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
    MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
    m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (let m := route2 True True False False False False False False False False False;
    CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
    CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
    ¬ MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
    NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
    MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
    m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (let m := route2 False True False True False True False True False True False;
    CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
    CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
    MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
    ¬ NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
    MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
    m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (let m := route2 False True False True False True False True False True True;
    CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
    CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
    MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
    NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
    ¬ MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
    m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (let m := route2 False True False True False False False True False True False;
    m.Structural ∧ m.Maximum false ∧ ¬ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
  (endless.Structural ∧ ¬ endless.Maximum 0 ∧ endless.Immaterial ∧ ¬ endless.HasIntellect 0) ∧
  -- bearers: one deletion per member other than excluded middle
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), ¬ MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    ¬ MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ ¬ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ ¬ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ ¬ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
  (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
    MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
    ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ ¬ RealizerSameBearer c) ∧
  -- state
  (∃ sf : StateFacts varying Nat, (∀ r, varyingBase r → ∃ s, r = sf.fact s) ∧
    sf.state 0 ≠ sf.state 1 ∧ BaseFixed varying varyingBase ∧
    SelectedAt varying varyingBase Rival 0 ∧ SelectedAt varying varyingBase Rival 1 ∧
    Contingent varying.arena 0 (sf.fact (sf.state 0)) ∧
    ∀ A, ¬ ReasonClosed varying.arena 0 A .target) ∧
  (∃ sf : StateFacts oneWay Unit, (∀ r, oneSource r → ∃ s, r = sf.fact s) ∧
    sf.state 0 = sf.state 1 ∧ BaseFixed oneWay oneSource ∧
    SelectedAt oneWay oneSource Rival 0 ∧ ¬ SelectedAt oneWay oneSource Rival 1) ∧
  -- capacity
  (∃ response, NecessaryAt ground.ontic 0 (some true) ∧
    ∀ w, Capacity ground.ontic.frame (exOf ground) response (some true) w) ∧
  (∀ response x w, ¬ Capacity law.ontic.frame (exOf law) response x w) ∧
  (∀ x, ¬ NecessaryAt law.ontic 0 x) ∧
  (∀ (φ : Nat → Fact → Fact → Fact → Prop) (base O : Fact → Prop) (w : Nat),
    SelectedAt ⟨ground, φ⟩ base O w ↔ SelectedAt ⟨law, φ⟩ base O w) ∧
  -- roots and conceivability
  TruthCore.Causality.RootMultiplication.Control.SurvivingRival ∧
  (¬ ConceivabilityExcludesNecessity (fun _ : Unit => True) (fun _ => True) ∧
    TestExtendsEqually (fun _ : Unit => True) () ()) ∧
  -- the ladder from the signature
  (Signature noMaximum ∧ noMaximum.Structural ∧ ¬ noMaximum.Maximum false ∧ noMaximum.Immaterial ∧
    ¬ noMaximum.HasIntellect false) ∧
  (Signature compositeRoot ∧ compositeRoot.Maximum false ∧ compositeRoot.Composite false ∧
    compositeRoot.MatterForm false ∧ (∀ y, ¬ compositeRoot.CausesIn y false compositeRoot.esse) ∧
    ¬ CompositeHasAUnitingCauseReading compositeRoot.Composite compositeRoot.CausesIn
      compositeRoot.esse ∧ ¬ compositeRoot.HasIntellect false) ∧
  (Signature simpleImpersonal ∧ simpleImpersonal.Structural ∧ simpleImpersonal.Maximum false ∧
    ¬ simpleImpersonal.Composite false ∧ ¬ simpleImpersonal.MatterForm false ∧
    ¬ simpleImpersonal.Immaterial ∧ ¬ simpleImpersonal.HasIntellect false) ∧
  (Signature willless ∧ willless.Structural ∧ willless.Maximum false ∧ willless.Immaterial ∧
    willless.HasIntellect false ∧ ¬ WillFollowsIntellectReading willless.HasIntellect willless.HasWill ∧
    ¬ willless.HasWill false) ∧
  (Signature classicalRoute ∧ classicalRoute.Structural ∧ classicalRoute.Maximum false ∧
    classicalRoute.Immaterial ∧ classicalRoute.HasIntellect false ∧ classicalRoute.HasWill false) ∧
  -- coverage of the shared explananda
  (SomethingNecessarily powers false ∧ SomethingNecessarily rotating false ∧
    (∀ x, ¬ NecessaryAt rotating false x) ∧ ¬ SomethingNecessarily law.ontic 0 ∧
    ¬ Explained ground 0 (.source true)) ∧
  (Contingent ground 0 .target ∧ ground.explains 0 (.source true) .target ∧
    ground.holds 1 (.source true) ∧ ¬ ground.holds 1 .target ∧
    NecessaryAt idle.ontic 0 (some true) ∧ Contingent idle 0 .target ∧ ¬ Explained idle 0 .target) ∧
  (NecessaryAt (onlyActual true) false false ∧ ¬ NecessaryAt (onlyActual false) false false ∧
    (onlyActual true).ExistsAt = (onlyActual false).ExistsAt) ∧
  (Marks acting twoSources Rival 0 ∧ MarksRequirePerson acting twoSources Rival 0 (fun _ => True) ∧
    ¬ MarksRequirePerson acting twoSources Rival 0 (fun _ => False))

end TruthCore.Alternatives.PhysicalGround
