import TruthCore.Modal.SelectedEffectBridge
import TruthCore.Explanation.ExplanatorySymmetry
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Greek.Aristotle.MetaphysicsIX

/-!
# Rigid act, simplicity and contingent creation (#555)

Three certificates. `Core` is the propositional modal K bundle of #555 on the #462
`OutputProfile`: the same rigid act token at every accessible world, strict efficacy and a
contingent effect, with a deletion model per member and the description trap. It uses no
necessity of the bearer. `RootExposure` applies two root-route readings, world by world, to a
field of decrees: `PotencyIsUnactualizedCapacityReading` and `IsImmutable`. The bridge
`ModalCapacity` from accessible actuality to ability is an open, unattributed premise here.

No clause says that divine simplicity entails any of these. Worlds are modal alternatives and
acts are overlay tokens. Nothing is asserted of reality; every model is analyst-built and shows
only that a formal bundle is satisfiable. `BranchCosts` restates the trilemma for an admitted
reason in the #755 arena and records what each deletion costs by the #750 standards. Mathlib enters through the #742 import, so these
results permit the Mathlib three. See `docs/notes/simplicity-collapse-555.md`.
-/
namespace TruthCore.Modal.SimplicityCollapse

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Case.Catholicism (IsImmutable)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)

variable {W B A R F : Type}

/-! ## The rigid token -/

/-- `□(A → C)` for one rigid token and one rigid effect, as a strict conditional from `w`. -/
def StrictEfficacy (p : OutputProfile W B A) (w : W) (a : A) (x : B) : Prop :=
  ∀ v, p.ontic.frame.access w v → p.performs v a → p.ontic.ExistsAt v x

/-- Wherever the bearer exists, the token is performed. A one-way consequence of reading the
token as the bearer's own being; it is weaker than an identity of act and being. -/
def BeingCarriesAct (p : OutputProfile W B A) (a : A) : Prop :=
  ∀ v, p.ontic.ExistsAt v p.source → p.performs v a

/-! ## The description -/

/-- Whatever the world-relative description denotes at a world is performed there. -/
def DescriptionSound (p : OutputProfile W B A) (d : W → Option A) : Prop :=
  ∀ v a, d v = some a → p.performs v a

/-- At each accessible world where the effect exists, the description denotes some act. -/
def CoversEffect (p : OutputProfile W B A) (d : W → Option A) (w : W) (x : B) : Prop :=
  ∀ v, p.ontic.frame.access w v → p.ontic.ExistsAt v x → ∃ a, d v = some a

/-- The description denotes the same token at each accessible world. -/
def RigidAt (p : OutputProfile W B A) (d : W → Option A) (w : W) (a : A) : Prop :=
  ∀ v, p.ontic.frame.access w v → d v = some a

/-! ## Models -/

/-- A necessary source, an effect only at `false`, and no causal edge and no effect at `true`. -/
def noCreation : Ontic Bool EffectBeing where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = source ∨ (x = firstEffect ∧ w = false)
  Causes := fun w x y => w = false ∧ x = source ∧ y = firstEffect

/-- Deletes act necessity: the token is performed only at the world with the effect. -/
def optionalAct : OutputProfile Bool EffectBeing Unit where
  ontic := noCreation
  source := source
  performs := fun w _ => w = false
  output := fun w _ x => w = false ∧ x = firstEffect

/-- Deletes strict efficacy: the token is performed at both worlds of `noCreation`. -/
def inefficaciousAct : OutputProfile Bool EffectBeing Unit where
  ontic := noCreation
  source := source
  performs := fun _ _ => True
  output := fun w _ x => w = false ∧ x = firstEffect

/-- Deletes contingency: the token and the effect at both worlds of #462's `fixedEffects`. -/
def necessitarianAct : OutputProfile Bool EffectBeing Unit where
  ontic := fixedEffects
  source := source
  performs := fun _ _ => True
  output := fun _ _ x => x = firstEffect

/-- The description of `optionalAct`, denoting nothing at the world without the effect. -/
def partialDescription : Bool → Option Unit
  | false => some ()
  | true => none

/-- Each world of #462's `alternatingEffects` has its own performed token. -/
def perWorldTokens : OutputProfile Bool EffectBeing Bool where
  ontic := alternatingEffects
  source := source
  performs := fun w a => a = w
  output := fun w a x => a = w ∧ x = some w

/-- Two tokens, for a test of premises read of different items. -/
inductive Token
  | inItself
  | directed
  deriving DecidableEq

/-- `inItself` at both worlds and `directed` only at the world with the effect. -/
def twoTokens : OutputProfile Bool EffectBeing Token where
  ontic := noCreation
  source := source
  performs := fun w t => t = .inItself ∨ w = false
  output := fun w t x => t = .directed ∧ w = false ∧ x = firstEffect

/-- The propositional core and its controls.

1. In any frame, no token and effect have act necessity, strict efficacy and contingency. No
   clause concerns the bearer's necessity, and no frame condition is assumed.
2. #462's cross-world stability, causal realization, sound relata and an actual output give
   strict efficacy.
3. For a contingent effect, the token is not performed at some accessible world, or it is
   performed at an accessible world lacking the effect.
4. A deletion model per member, each with a necessary source and the token performed at
   `false`: `optionalAct`, `inefficaciousAct`, `necessitarianAct`.
5. A bearer necessary at `w` with `BeingCarriesAct` gives act necessity. `optionalAct` has a
   necessary bearer and lacks `BeingCarriesAct`.
6. A sound description rigid at `w` gives act necessity. On `optionalAct`, `partialDescription`
   is sound and covers the effect, and denotes nothing at `true`. On `perWorldTokens` a sound
   description denotes a token at every accessible world, and no token has act necessity.
7. The first clause with act necessity read of `a` and efficacy of `b` needs `a = b`: if they
   are equal the bundle is inconsistent, and `twoTokens` has act necessity of one token, strict
   efficacy of the other and a contingent effect, with each clause failing of the other token. -/
def Core : Prop :=
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a : A) (x : B),
    SameActEverywhere p w a → StrictEfficacy p w a x → ¬ ContingentAt p.ontic w x) ∧
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a : A) (x : B),
    SoundDistinctCauses p.ontic → RealizedOutputs p → StableActOutput p w a → p.output w a x →
    StrictEfficacy p w a x) ∧
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a : A) (x : B),
    ContingentAt p.ontic w x →
    (∃ v, p.ontic.frame.access w v ∧ ¬ p.performs v a) ∨
      ∃ v, p.ontic.frame.access w v ∧ p.performs v a ∧ ¬ p.ontic.ExistsAt v x) ∧
  -- delete act necessity
  (NecessaryAt optionalAct.ontic false optionalAct.source ∧ optionalAct.performs false () ∧
    ¬ SameActEverywhere optionalAct false () ∧ StrictEfficacy optionalAct false () firstEffect ∧
    ContingentAt optionalAct.ontic false firstEffect) ∧
  -- delete strict efficacy
  (NecessaryAt inefficaciousAct.ontic false inefficaciousAct.source ∧
    inefficaciousAct.performs false () ∧ SameActEverywhere inefficaciousAct false () ∧
    ¬ StrictEfficacy inefficaciousAct false () firstEffect ∧
    ContingentAt inefficaciousAct.ontic false firstEffect) ∧
  -- delete contingency
  (NecessaryAt necessitarianAct.ontic false necessitarianAct.source ∧
    necessitarianAct.performs false () ∧ SameActEverywhere necessitarianAct false () ∧
    StrictEfficacy necessitarianAct false () firstEffect ∧
    ¬ ContingentAt necessitarianAct.ontic false firstEffect) ∧
  -- the bearer
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a : A),
    NecessaryAt p.ontic w p.source → BeingCarriesAct p a → SameActEverywhere p w a) ∧
  ¬ BeingCarriesAct optionalAct () ∧
  -- the description
  (∀ (W B A : Type) (p : OutputProfile W B A) (d : W → Option A) (w : W) (a : A),
    DescriptionSound p d → RigidAt p d w a → SameActEverywhere p w a) ∧
  (DescriptionSound optionalAct partialDescription ∧
    CoversEffect optionalAct partialDescription false firstEffect ∧
    partialDescription false = some () ∧ partialDescription true = none) ∧
  (DescriptionSound perWorldTokens some ∧
    (∀ v, perWorldTokens.ontic.frame.access false v → ∃ a, (some v : Option Bool) = some a) ∧
    ∀ a, ¬ SameActEverywhere perWorldTokens false a) ∧
  -- two items
  (∀ (W B A : Type) (p : OutputProfile W B A) (w : W) (a b : A) (x : B),
    a = b → SameActEverywhere p w a → StrictEfficacy p w b x → ¬ ContingentAt p.ontic w x) ∧
  (SameActEverywhere twoTokens false .inItself ∧
    StrictEfficacy twoTokens false .directed firstEffect ∧
    ContingentAt twoTokens.ontic false firstEffect ∧
    ¬ StrictEfficacy twoTokens false .inItself firstEffect ∧
    ¬ SameActEverywhere twoTokens false .directed)

/-! ## The root-route readings -/

/-- Open bridge: being actually in a respect at a world accessible from `w` suffices for being
able to be so at `w`. Unattributed. It reads `CanBe` modally; the source example of ability is
the knower who is able to contemplate. -/
def ModalCapacity (m : Ontic W B) (InAct CanBe : W → B → R → Prop) (w : W) (g : B) : Prop :=
  ∀ v r, m.frame.access w v → InAct v g r → CanBe w g r

/-- The Metaphysics IX.6 reading and `IsImmutable` for `g`, at world `w`, with `ModalCapacity`. -/
def ReadingsAt (m : Ontic W B) (InAct InPotency CanBe : W → B → R → Prop) (w : W) (g : B) : Prop :=
  PotencyIsUnactualizedCapacityReading (InAct w) (InPotency w) (CanBe w) ∧
    IsImmutable (InPotency w) g ∧ ModalCapacity m InAct CanBe w g

/-- At most one field member is a respect in which `g` is in act at `w`. -/
def ExclusiveDecree (InAct : W → B → R → Prop) (O : R → Prop) (w : W) (g : B) : Prop :=
  ∀ d e, O d → O e → InAct w g d → InAct w g e → d = e

/-- Some field member is a respect in which `g` is in act at `v`. -/
def SomeDecree (InAct : W → B → R → Prop) (O : R → Prop) (v : W) (g : B) : Prop :=
  ∃ e, O e ∧ InAct v g e

/-- Wherever accessible `g` is in act in respect `d`, the effect exists. -/
def RespectSuffices (m : Ontic W B) (InAct : W → B → R → Prop) (w : W) (g : B) (d : R) (x : B) :
    Prop :=
  ∀ v, m.frame.access w v → InAct v g d → m.ExistsAt v x

/-- The members of the decree bundle other than the readings: a field member `d` true of `g`
at `w`, at most one at `w`, some at each accessible world, `d` sufficing for `x`, and `x`
contingent at `w`. -/
def Decreed (m : Ontic W B) (InAct : W → B → R → Prop) (O : R → Prop) (w : W) (g : B) (d : R)
    (x : B) : Prop :=
  O d ∧ InAct w g d ∧ ExclusiveDecree InAct O w g ∧
    (∀ v, m.frame.access w v → SomeDecree InAct O v g) ∧
    RespectSuffices m InAct w g d x ∧ ContingentAt m w x

/-! ## Models of the decree bundle

All on `noCreation`, with source `source`, effect `firstEffect` and decree `false` at world
`false`, unless stated. Respects are `Bool`, and the field is every respect. -/

/-- Each world's decree is its own label. -/
def labelAct : Bool → EffectBeing → Bool → Prop := fun w _ r => r = w

/-- No being is able to be anything. -/
def noAbility {R : Type} : Bool → EffectBeing → R → Prop := fun _ _ _ => False

/-- Every being is able to be anything. Respects are arbitrary. -/
def fullAbility {R : Type} : Bool → EffectBeing → R → Prop := fun _ _ _ => True

/-- Potency exactly as the Metaphysics IX.6 reading gives it from full ability and `labelAct`. -/
def labelPotency : Bool → EffectBeing → Bool → Prop := fun w _ r => ¬ labelAct w source r

/-- The decree `false` at world `false` and no respect at `true`. -/
def actualOnlyAct : Bool → EffectBeing → Bool → Prop := fun w _ r => w = false ∧ r = false

/-- Ability to be so: `false` only, at each world. -/
def falseAbility : Bool → EffectBeing → Bool → Prop := fun _ _ r => r = false

/-- Potency as the reading gives it from `falseAbility` and `actualOnlyAct`. -/
def actualOnlyPotency : Bool → EffectBeing → Bool → Prop :=
  fun w x r => falseAbility w x r ∧ ¬ actualOnlyAct w x r

/-- Every respect at `false` and `true` only at `true`. -/
def allAtActual : Bool → EffectBeing → Bool → Prop := fun w _ r => w = false ∨ r = true

/-- Decree `false` at both worlds. -/
def constantAct : Bool → EffectBeing → Bool → Prop := fun _ _ r => r = false

/-- Decree `true` at both worlds, also read as the ability that matches it. -/
def otherAct : Bool → EffectBeing → Bool → Prop := fun _ _ r => r = true

/-- `noCreation` with access from `false` to both worlds and none from `true`. -/
def noReturn : Ontic Bool EffectBeing where
  frame := ⟨fun u _ => u = false⟩
  ExistsAt := noCreation.ExistsAt
  Causes := noCreation.Causes

/-- The single respect of the branch where no decree is a respect. -/
def oneRespect : Bool → EffectBeing → Unit → Prop := fun _ _ _ => True

/-- The root-route exposure. Each clause is conditional or a verdict on a named model.

1. If the readings hold at `w`, no respect of `g` true at an accessible world is false at `w`.
2. With the readings at `w`, a decree `d` of `g` at `w`, at most one decree at `w`, a decree at
   each accessible world, and `d` sufficing for `x` at them, `x` is not contingent at `w`.
3. With the readings at `v`, `w` accessible from `v` and a respect true at `w`, it is true at `v`.
4. For a contingent `x` given a decree at `w` sufficing for `x`, with potency reading,
   immutability and at most one decree at `w`: some accessible world lacking `x` has no decree,
   or `ModalCapacity` fails at `w`.
5. A deletion model per member of the second clause.
6. Controls of the third clause: `actualOnlyAct` keeps the readings at `false` with a contingent
   effect and fails immutability at `true`; on `noReturn` the readings hold at both worlds, the
   decree is true at `false` and false at `true`, and `false` is not accessible from `true`.
7. The branch where no decree is a respect: `oneRespect` has the readings at both worlds, the
   same respects at both, no respect sufficing for the effect, and a contingent effect with
   strict efficacy of `directed`.
8. Selection: a one-member base has no `Marks`. With that member true throughout, base-fixed
   favouring, net selection and exactly one true field member at each world, no field member is
   contingent. #742's `acting` has `Marks` on two necessary reasons, a contingent target, and no
   net selection at `0` or `1`.
9. A condition: with act necessity and `□(A ∧ S → C)`, a true `S` is contingent if `C` is. Then
   no account of `S` is reason-closed and founded with all reasons necessitating. #750's models
   witness each other option: `brute` has no reason-closed account, `chain` has a reason-closed
   account that is not founded, and `ground` a reason-closed founded account with a
   nonnecessitating reason. `S` may be `C` itself, so a condition as such explains nothing. -/
def RootExposure : Prop :=
  (∀ (W B R : Type) (m : Ontic W B) (InAct InPotency CanBe : W → B → R → Prop) (w v : W) (g : B)
      (r : R),
    ReadingsAt m InAct InPotency CanBe w g → m.frame.access w v → InAct v g r → InAct w g r) ∧
  (∀ (W B R : Type) (m : Ontic W B) (InAct InPotency CanBe : W → B → R → Prop) (O : R → Prop)
      (w : W) (g x : B) (d : R),
    ReadingsAt m InAct InPotency CanBe w g → O d → InAct w g d →
    ExclusiveDecree InAct O w g → (∀ v, m.frame.access w v → SomeDecree InAct O v g) →
    RespectSuffices m InAct w g d x → ¬ ContingentAt m w x) ∧
  (∀ (W B R : Type) (m : Ontic W B) (InAct InPotency CanBe : W → B → R → Prop) (w v : W) (g : B)
      (r : R),
    ReadingsAt m InAct InPotency CanBe v g → m.frame.access v w → InAct w g r → InAct v g r) ∧
  (∀ (W B R : Type) (m : Ontic W B) (InAct InPotency CanBe : W → B → R → Prop) (O : R → Prop)
      (w : W) (g x : B) (d : R),
    PotencyIsUnactualizedCapacityReading (InAct w) (InPotency w) (CanBe w) →
    IsImmutable (InPotency w) g → O d → InAct w g d → ExclusiveDecree InAct O w g →
    RespectSuffices m InAct w g d x → ContingentAt m w x →
    (∃ v, m.frame.access w v ∧ ¬ m.ExistsAt v x ∧ ¬ SomeDecree InAct O v g) ∨
      ¬ ModalCapacity m InAct CanBe w g) ∧
  -- delete the potency reading
  (¬ PotencyIsUnactualizedCapacityReading (labelAct false) (noAbility false) (fullAbility false) ∧
    IsImmutable (noAbility (R := Bool) false) source ∧ ModalCapacity noCreation labelAct fullAbility false source ∧
    Decreed noCreation labelAct (fun _ => True) false source false firstEffect) ∧
  -- delete immutability
  (PotencyIsUnactualizedCapacityReading (labelAct false) (labelPotency false) (fullAbility false) ∧
    ¬ IsImmutable (labelPotency false) source ∧
    ModalCapacity noCreation labelAct fullAbility false source ∧
    Decreed noCreation labelAct (fun _ => True) false source false firstEffect) ∧
  -- delete `ModalCapacity`
  (PotencyIsUnactualizedCapacityReading (labelAct false) (noAbility false) (noAbility false) ∧
    IsImmutable (noAbility (R := Bool) false) source ∧ ¬ ModalCapacity noCreation labelAct noAbility false source ∧
    Decreed noCreation labelAct (fun _ => True) false source false firstEffect) ∧
  -- delete field membership of the actual decree
  (ReadingsAt noCreation allAtActual noAbility fullAbility false source ∧
    ¬ (fun r : Bool => r = true) false ∧ allAtActual false source false ∧
    ExclusiveDecree allAtActual (fun r => r = true) false source ∧
    (∀ v, noCreation.frame.access false v → SomeDecree allAtActual (fun r => r = true) v source) ∧
    RespectSuffices noCreation allAtActual false source false firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- delete the actual decree
  (ReadingsAt noCreation otherAct noAbility otherAct false source ∧ ¬ otherAct false source false ∧
    ExclusiveDecree otherAct (fun _ => True) false source ∧
    (∀ v, noCreation.frame.access false v → SomeDecree otherAct (fun _ => True) v source) ∧
    RespectSuffices noCreation otherAct false source false firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- delete exclusivity
  (ReadingsAt noCreation allAtActual noAbility fullAbility false source ∧
    allAtActual false source false ∧
    ¬ ExclusiveDecree allAtActual (fun _ => True) false source ∧
    (∀ v, noCreation.frame.access false v → SomeDecree allAtActual (fun _ => True) v source) ∧
    RespectSuffices noCreation allAtActual false source false firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- delete a decree at each accessible world
  (ReadingsAt noCreation actualOnlyAct actualOnlyPotency falseAbility false source ∧
    actualOnlyAct false source false ∧
    ExclusiveDecree actualOnlyAct (fun _ => True) false source ∧
    ¬ SomeDecree actualOnlyAct (fun _ => True) true source ∧
    RespectSuffices noCreation actualOnlyAct false source false firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- delete sufficiency of the decree
  (ReadingsAt noCreation constantAct noAbility falseAbility false source ∧
    constantAct false source false ∧
    ExclusiveDecree constantAct (fun _ => True) false source ∧
    (∀ v, noCreation.frame.access false v → SomeDecree constantAct (fun _ => True) v source) ∧
    ¬ RespectSuffices noCreation constantAct false source false firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- delete contingency
  (ReadingsAt fixedEffects constantAct noAbility falseAbility false source ∧
    constantAct false source false ∧
    ExclusiveDecree constantAct (fun _ => True) false source ∧
    (∀ v, fixedEffects.frame.access false v → SomeDecree constantAct (fun _ => True) v source) ∧
    RespectSuffices fixedEffects constantAct false source false firstEffect ∧
    ¬ ContingentAt fixedEffects false firstEffect) ∧
  -- controls of the third clause
  (ReadingsAt noCreation actualOnlyAct actualOnlyPotency falseAbility false source ∧
    ¬ IsImmutable (actualOnlyPotency true) source ∧
    ContingentAt noCreation false firstEffect) ∧
  (ReadingsAt noReturn actualOnlyAct noAbility actualOnlyAct false source ∧
    ReadingsAt noReturn actualOnlyAct noAbility actualOnlyAct true source ∧
    actualOnlyAct false source false ∧ ¬ actualOnlyAct true source false ∧
    ¬ noReturn.frame.access true false ∧ ContingentAt noReturn false firstEffect) ∧
  -- no decree is a respect
  (ReadingsAt noCreation oneRespect noAbility fullAbility false source ∧
    ReadingsAt noCreation oneRespect noAbility fullAbility true source ∧
    (∀ r, oneRespect false source r ↔ oneRespect true source r) ∧
    (∀ r, ¬ RespectSuffices noCreation oneRespect false source r firstEffect) ∧
    twoTokens.ontic = noCreation ∧ StrictEfficacy twoTokens false .directed firstEffect ∧
    ContingentAt noCreation false firstEffect) ∧
  -- selection
  (∀ (W B F : Type) (X : TruthCore.Explanation.ExplanatorySymmetry.Frame W B F) (act : F) (O : F → Prop) (a : W),
    ¬ Marks X (· = act) O a) ∧
  (∀ (W B F : Type) (X : TruthCore.Explanation.ExplanatorySymmetry.Frame W B F) (act : F) (O : F → Prop) (a : W) (f : F),
    (∀ v, Worlds X.arena a v → X.arena.holds v act) → BaseFixed X (· = act) →
    (∀ w, Worlds X.arena a w → SelectedAt X (· = act) O w) →
    (∀ w, Worlds X.arena a w → ExhaustiveAt X.arena O w) →
    (∀ w, Worlds X.arena a w → ExclusiveAt X.arena O w) →
    O f → ¬ Contingent X.arena a f) ∧
  (Marks acting twoSources Rival 0 ∧ NecessaryBase acting.arena twoSources 0 ∧
    Contingent acting.arena 0 .target ∧
    ¬ NetSelects acting twoSources 0 .target .other ∧
    ¬ NetSelects acting twoSources 1 .other .target) ∧
  -- a condition
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (act s c : F),
    (∀ v, Access A a v → A.holds v act) →
    (∀ v, Access A a v → A.holds v act → A.holds v s → A.holds v c) →
    A.holds a s → Contingent A a c → Contingent A a s) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (s : F),
    Contingent A a s → ReasonClosed A a S s → Founded A a S → ¬ AllReasonsNecessitate A a S) ∧
  ((∀ S, ¬ ReasonClosed brute 0 S .target) ∧ Contingent brute 0 .target) ∧
  (ReasonClosed chain 0 Members .target ∧ Contingent chain 0 .target ∧ ¬ Founded chain 0 Members) ∧
  (ReasonClosed ground 0 OneSource .target ∧ Contingent ground 0 .target ∧
    Founded ground 0 OneSource ∧ ¬ AllReasonsNecessitate ground 0 OneSource) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (act c : F),
    Contingent A a c →
    ∃ s, (∀ v, Access A a v → A.holds v act → A.holds v s → A.holds v c) ∧ Contingent A a s)

/-! ## What each branch costs -/

/-- `r` is true at every world accessible from `a`. -/
def NecessaryFact (A : Arena W B F) (a : W) (r : F) : Prop :=
  ∀ v, Access A a v → A.holds v r

/-- `r` strictly suffices for `f` from `a`. It is the modal half of the necessitating sense of
"explains"; admission as a reason (`A.explains`) is a separate relation and does not imply it. -/
def Necessitates (A : Arena W B F) (a : W) (r f : F) : Prop :=
  ∀ v, Access A a v → A.holds v r → A.holds v f

/-- Truth where the source (`source true`) is necessary, the act (`source false`) holds only at
`0`, and the effect holds at `0` and `1`, so another way to the effect is left open at `1`. -/
def relocatedHolds : Nat → Fact → Prop
  | w, .target => w = 0 ∨ w = 1
  | _, .other => False
  | w, .source i => i = true ∨ w = 0
  | _, .member _ => False
  | _, .whole => False

/-- The source is a reason for the act and the act is a reason for the effect. -/
inductive RelocatedReason : Nat → Fact → Fact → Prop
  | toAct : RelocatedReason 0 (.source true) (.source false)
  | toEffect : RelocatedReason 0 (.source false) .target

/-- An optional act that necessitates its effect, with a necessary source that does not
necessitate the act. -/
def relocated : Arena Nat (Option Bool) Fact := rival relocatedHolds RelocatedReason

/-- The account of `relocated`: effect, act and source. -/
inductive RelocatedAccount : Fact → Prop
  | target : RelocatedAccount .target
  | act : RelocatedAccount (.source false)
  | source : RelocatedAccount (.source true)

/-- The trilemma at the level of an admitted reason, and the cost of each deletion.

1. No reason is necessary, necessitates its explanandum, and has a contingent explanandum.
2. For a contingent target with a reason-closed founded account: not every reason necessitates,
   the account is not contrast-relevant, and not every reason for a contingent member is
   contingent. This holds of every branch below that keeps a contingent target.
3. Keep the necessary reason and contingency, delete necessitation: `ground`. The source is
   necessary and admitted for the contingent target, and does not necessitate it. The account is
   closed and founded, and nothing in it excludes the target's rival world.
4. Keep necessitation and contingency, delete the necessary reason: `relocated`. The act is
   contingent, admitted for the effect, necessitates it and is false at each rival world of the
   effect. The account is closed and founded. The act's own reason is the necessary source,
   which does not necessitate it and is true at the act's rival world `1`. So the first gap has
   moved one step back and is not removed.
5. Keep the necessary reason and necessitation, delete contingency: `necessitarian`. No fact is
   contingent, every reason necessitates, and contrast relevance holds only vacuously.

Only `explains` as admitted is shared by the three models; clause 1 fires only on `Necessitates`.
No model is asserted of reality, and none is a reading of divine simplicity. -/
def BranchCosts : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (r f : F),
    NecessaryFact A a r → Necessitates A a r f → ¬ Contingent A a f) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    Contingent A a x → ReasonClosed A a S x → Founded A a S →
    ¬ AllReasonsNecessitate A a S ∧ ¬ ContrastRelevant A a S ∧ ¬ AllReasonsVary A a S) ∧
  -- delete necessitation
  (NecessaryFact ground 0 (.source true) ∧ ground.explains 0 (.source true) .target ∧
    ¬ Necessitates ground 0 (.source true) .target ∧ Contingent ground 0 .target ∧
    ReasonClosed ground 0 OneSource .target ∧ Founded ground 0 OneSource ∧
    ¬ ContrastRelevant ground 0 OneSource) ∧
  -- delete the necessary reason
  (¬ NecessaryFact relocated 0 (.source false) ∧ relocated.explains 0 (.source false) .target ∧
    Necessitates relocated 0 (.source false) .target ∧ Contingent relocated 0 .target ∧
    (∀ v, Access relocated 0 v → ¬ relocated.holds v .target → ¬ relocated.holds v (.source false)) ∧
    ReasonClosed relocated 0 RelocatedAccount .target ∧ Founded relocated 0 RelocatedAccount ∧
    NecessaryFact relocated 0 (.source true) ∧ relocated.explains 0 (.source true) (.source false) ∧
    ¬ Necessitates relocated 0 (.source true) (.source false) ∧
    ¬ relocated.holds 1 (.source false) ∧
    (∀ r, relocated.explains 0 r (.source false) → relocated.holds 1 r) ∧
    ¬ ContrastRelevant relocated 0 RelocatedAccount) ∧
  -- delete contingency
  (NecessaryFact necessitarian 0 (.source true) ∧ necessitarian.explains 0 (.source true) .target ∧
    Necessitates necessitarian 0 (.source true) .target ∧
    (∀ f, ¬ Contingent necessitarian 0 f) ∧
    ReasonClosed necessitarian 0 OneSource .target ∧ Founded necessitarian 0 OneSource ∧
    AllReasonsNecessitate necessitarian 0 OneSource ∧ ContrastRelevant necessitarian 0 OneSource)

end TruthCore.Modal.SimplicityCollapse
