module

public import TruthCore.Explanation.StoppingPoints
public import TruthCore.Logic.ExcludedMiddle

/-!
# Local truthmakers versus one ground of a necessary existential fact (#485)

An analyst-defined conditional map, not a sourced argument. It asks whether a
necessary existential disjunction ("something exists", true at every accessible
world) can have only contingent, world-local grounds, and what the step to a
necessarily existing individual needs. It reuses the arena, factivity, coherence
and necessitation of `PSRStrength` and `NecessaryFact` of `StoppingPoints`, with no
new primitive relation.

Four things are kept apart:
* a **local ground**: at each accessible world some reason for the existential fact
  holds there (`□ ∃ r`), which may be a different reason at each world;
* a **uniform ground**: one reason serves at every accessible world (`∃ r □`);
* an **instance ground** (truthmaker reading): a reason for the existential fact is
  the existence fact of some individual;
* an **efficient producer**: the separate `Ontic.Causes` relation, never inferred
  from `explains`.

`explains` keeps the reading of `PSRStrength` ("admitted as a reason why"); it is
not assumed to be full metaphysical ground, causal, or necessitating. The models
show that encoded bundles are satisfiable, not that they are metaphysically
possible. See `docs/notes/disjunction-ground-485.md` for the reading, the rival
replies and the open bridges.
-/

@[expose] public section

namespace TruthCore.Explanation.DisjunctionGround

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.StoppingPoints (NecessaryFact)
open TruthCore.German.Kant.CosmologicalInference

variable {W B F : Type}

/-- `d` is the existential fact of the arena: true at a world exactly when some
candidate individual exists there. For a two-member roster it is the disjunction
`E a ∨ E b`. Concreteness is not modelled; `ExistsAt` is the only predicate. -/
def ExistentialFact (A : Arena W B F) (d : F) : Prop :=
  ∀ v, A.holds v d ↔ ∃ x, A.ontic.ExistsAt v x

/-- Local grounds (`□ ∃ r`): at every world accessible from `a`, `d` has some
reason there. The reason may vary with the world. -/
def LocallyGrounded (A : Arena W B F) (a : W) (d : F) : Prop :=
  ∀ v, Access A a v → Explained A v d

/-- A uniform ground (`∃ r □`): one and the same fact is a reason for `d` at every
world accessible from `a`. -/
def UniformGround (A : Arena W B F) (a : W) (d : F) : Prop :=
  ∃ r, ∀ v, Access A a v → A.explains v r d

/-- The instance (truthmaker) reading of grounds of `d`: every reason for `d`, at
any world, is the existence fact of some individual. This is the extra bridge from
facts to bearers; it excludes an abstract law or structural rule as a reason. -/
def InstanceGrounding (A : Arena W B F) (d : F) : Prop :=
  ∀ v r, A.explains v r d → ∃ x, r = A.exist x

/-! ## Models -/

/-- Facts of the models: each individual's existence, the existential fact, and a
law-like fact that is not the existence fact of any individual. -/
inductive DFact | exist (x : Bool) | some | law

/-- Two worlds, two rigid individuals, no causation, identity as conjunct relation. -/
def mk (access : Bool → Bool → Prop) (ex : Bool → Bool → Prop)
    (holds : Bool → DFact → Prop) (explains : Bool → DFact → DFact → Prop) :
    Arena Bool Bool DFact where
  ontic := {
    frame := ⟨access⟩
    ExistsAt := ex
    Causes := fun _ _ _ => False }
  holds := holds
  exist := .exist
  explains := explains
  conjunct := fun g f => g = f

/-- Alternating existence: individual `x` exists only at world `x` (#445). -/
def alternating (w x : Bool) : Prop := x = w

/-- Truth in the alternating models: each existence fact where its individual
exists, the existential fact everywhere, and the law nowhere or everywhere. -/
def altHolds (lawTrue : Bool) : Bool → DFact → Prop
  | w, .exist x => x = w
  | _, .some => True
  | _, .law => lawTrue = true

/-- Only the existence fact of the named individual is a reason, and only for the
existential fact. -/
def existReason (pick : Bool → Bool → Prop) : Bool → DFact → DFact → Prop
  | w, .exist x, .some => pick w x
  | _, .exist _, .exist _ => False
  | _, .exist _, .law => False
  | _, .some, _ => False
  | _, .law, _ => False

/-- Local truthmakers: at each world the existence of the individual there is the
reason for the existential fact. Local grounds, no uniform ground. -/
def truthmakers : Arena Bool Bool DFact :=
  mk everywhere alternating (altHolds false) (existReason fun w x => x = w)

/-- The abstract-rule rival: a necessary law is the reason for the existential fact
at every world, and nothing else is a reason. -/
def lawGround : Arena Bool Bool DFact :=
  mk everywhere alternating (altHolds true) fun _ r f => match r, f with
    | .law, .some => True
    | .law, .exist _ => False
    | .law, .law => False
    | .some, _ => False
    | .exist _, _ => False

/-- Deletes factivity: the existence fact of `false` is the reason at both worlds,
though it is false at world `true`. -/
def nonfactive : Arena Bool Bool DFact :=
  mk everywhere alternating (altHolds false) (existReason fun _ x => x = false)

/-- Deletes coherence: every existence fact is true everywhere, though each
individual exists only at its own world. -/
def incoherent : Arena Bool Bool DFact :=
  mk everywhere alternating
    (fun _ f => match f with
      | .exist _ => True
      | .some => True
      | .law => False)
    (existReason fun _ x => x = false)

/-- Deletes actual reflexivity: world `false` sees only world `true`, where only
individual `true` exists. -/
def onlyTrue (w x : Bool) : Prop := w = true ∧ x = true

/-- The non-reflexive deletion model. -/
def unseenActual : Arena Bool Bool DFact :=
  mk (fun _ v => v = true) onlyTrue
    (fun w f => match f with
      | .exist x => onlyTrue w x
      | .some => w = true
      | .law => False)
    (existReason onlyTrue)

/-- Individual `true` exists everywhere, `false` only at world `false`. -/
def fixedExists (w x : Bool) : Prop := x = true ∨ x = w

/-- Deletes the absence of a necessary being: the existence fact of the fixed
individual is the reason at both worlds. It causes nothing. -/
def fixedBearer : Arena Bool Bool DFact :=
  mk everywhere fixedExists
    (fun w f => match f with
      | .exist x => fixedExists w x
      | .some => True
      | .law => False)
    (existReason fun _ x => x = true)

/-! ## Certificate -/

/-- The local/uniform/instance map for a necessary existential fact.

General theorems:
1. A uniform ground gives local grounds.
2. Under factivity, local grounds make the grounded fact necessary.
3. Under factivity, coherence and the instance reading, local grounds give an
   existent at every accessible world: necessary population, de dicto.
4. The positive bridge theorem: under factivity, coherence, the instance reading and
   actual reflexivity, a uniform ground gives a necessary being.
5. The fork, classically: under factivity, coherence and actual reflexivity, a
   uniform ground is either a reason that is no individual's existence fact, or
   there is a necessary being. The horns are not claimed exclusive.

Models:
* `truthmakers` keeps every premise of 4 except the uniform ground, and has a
  necessary existential fact, necessitating local grounds, a contingent disjunct and
  no necessary being: necessity of the disjunction with only contingent grounds.
* `lawGround` keeps every premise of 4 except the instance reading: a necessary,
  necessitating, uniform reason, no causation and no necessary being. It is the
  left horn of 5.
* `nonfactive`, `incoherent` and `unseenActual` keep every other premise of 4 and
  delete factivity, coherence and actual reflexivity respectively, with no necessary
  being; `unseenActual` has an individual necessary at the selected world that does
  not actually exist there.
* `fixedBearer` satisfies every premise of 4, so they are jointly satisfiable; its
  necessary individual grounds the existential fact and causes nothing, beside an
  actual contingent individual with no cause.

So inclusion-minimality of the premise set of 4 together with the absence of a
necessary being is certified by the five deletion models. -/
def DisjunctionGroundMap : Prop :=
  -- 1. ∃ □ to □ ∃
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (d : F),
    UniformGround A a d → LocallyGrounded A a d) ∧
  -- 2. local grounds and factivity give necessity of the fact
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (d : F),
    Factive A → LocallyGrounded A a d → NecessaryFact A a d) ∧
  -- 3. local instance grounds give necessary population
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (d : F),
    Factive A → Coherent A → InstanceGrounding A d → LocallyGrounded A a d →
      ∀ v, Access A a v → ∃ x, A.ontic.ExistsAt v x) ∧
  -- 4. the bridge theorem
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (d : F),
    Factive A → Coherent A → InstanceGrounding A d → Access A a a →
      UniformGround A a d → NecessaryBeing A.ontic a) ∧
  -- 5. the fork
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (d : F),
    TruthCore.Logic.ExcludedMiddle → Factive A → Coherent A → Access A a a →
      UniformGround A a d →
      (∃ r, (∀ v, Access A a v → A.explains v r d) ∧ ¬ ∃ x, r = A.exist x) ∨
        NecessaryBeing A.ontic a) ∧
  -- local truthmakers only: the disjunction is necessary and no individual is
  (Factive truthmakers ∧ Coherent truthmakers ∧ InstanceGrounding truthmakers .some ∧
    Access truthmakers false false ∧ ExistentialFact truthmakers .some ∧
    LocallyGrounded truthmakers false .some ∧ NecessaryFact truthmakers false .some ∧
    Necessitating truthmakers ∧ Contingent truthmakers false (.exist false) ∧
    ¬ UniformGround truthmakers false .some ∧ ¬ NecessaryBeing truthmakers.ontic false) ∧
  -- the abstract rule: uniform and necessitating, no instance, no necessary being
  (Factive lawGround ∧ Coherent lawGround ∧ ¬ InstanceGrounding lawGround .some ∧
    Access lawGround false false ∧ ExistentialFact lawGround .some ∧
    UniformGround lawGround false .some ∧ NecessaryFact lawGround false .law ∧
    Necessitating lawGround ∧ Contingent lawGround false (.exist false) ∧
    (∀ w y x, ¬ lawGround.ontic.Causes w y x) ∧ ¬ NecessaryBeing lawGround.ontic false) ∧
  -- delete factivity
  (¬ Factive nonfactive ∧ Coherent nonfactive ∧ InstanceGrounding nonfactive .some ∧
    Access nonfactive false false ∧ UniformGround nonfactive false .some ∧
    ¬ NecessaryBeing nonfactive.ontic false) ∧
  -- delete coherence
  (Factive incoherent ∧ ¬ Coherent incoherent ∧ InstanceGrounding incoherent .some ∧
    Access incoherent false false ∧ UniformGround incoherent false .some ∧
    ¬ NecessaryBeing incoherent.ontic false) ∧
  -- delete actual reflexivity
  (Factive unseenActual ∧ Coherent unseenActual ∧ InstanceGrounding unseenActual .some ∧
    ¬ Access unseenActual false false ∧ UniformGround unseenActual false .some ∧
    NecessaryAt unseenActual.ontic false true ∧
    ¬ NecessaryBeing unseenActual.ontic false) ∧
  -- every premise of 4 at once: a necessary bearer that causes nothing
  (Factive fixedBearer ∧ Coherent fixedBearer ∧ InstanceGrounding fixedBearer .some ∧
    Access fixedBearer false false ∧ ExistentialFact fixedBearer .some ∧
    UniformGround fixedBearer false .some ∧ NecessaryBeing fixedBearer.ontic false ∧
    ContingentAt fixedBearer.ontic false false ∧
    (∀ w y x, ¬ fixedBearer.ontic.Causes w y x))

end TruthCore.Explanation.DisjunctionGround
