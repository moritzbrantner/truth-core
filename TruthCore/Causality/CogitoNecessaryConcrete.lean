import Mathlib.Logic.Relation
import TruthCore.Causality.BruteFoundationBoundary
import TruthCore.Logic.CogitoConcrete
import TruthCore.Logic.ExcludedMiddle

/-!
# From an occurring thought to a necessary concrete ground-ancestor of its bearer (#564)

Source-free and stipulative: nothing here is attributed to Descartes, Aristotle,
Aquinas or Kant, and nothing shows that any thought occurs.

The #536 Cogito trunk (`ThoughtOccurs`, `EveryThoughtHasSubject`) and its
concrete fork (`EveryBearerIsConcrete`, `EveryBearerExistsAt`) are reused
unchanged, instantiated at the `Profile` of #505/#510
(`TruthCore.Causality.BruteFoundationBoundary`): a Kant `Ontic` signature plus
a supplied concreteness predicate and a world-local grounding relation
`grounds w y x` ("y grounds x at w").

What the thinker adds. `necessaryConcreteOfGroundedContingents` (on `main`, not
a registered result) and #487's closed branch need two *global* premises:
well-foundedness of grounding over the whole candidate carrier, and that
*every* actual contingent concretum has an actual concrete ground. Starting from
the bearer of an occurring thought, two *thinker-local* premises suffice:

* `ThinkerGroundingAccessible`: below each bearer of an occurring thought there
  is no infinite descending chain of actual concrete grounds (`Acc`, not
  `WellFounded`);
* `ThinkerAncestryGrounded`: each contingent actual concrete ground-ancestor of
  such a bearer (the bearer included) has an actual concrete ground.

Each global premise implies its local one, and one finite model satisfies both
local premises while both global ones fail (`StrictlyWeakerModel`). In that
model the thinker exists at every accessible world and is not contingent: no
"the thinker is contingent" premise is used.

`ActualConcreteGround` keeps only grounds that are concrete and exist at `w`;
an abstract or absent ground is not counted, so a root here is a root *of this
relation*, not shown absolutely unexplained (`DEF-BRUTE-ROOT-RELATIVE-GROUNDING`).
`NecessaryAt` is accessibility-relative and de re over rigid candidate identity;
no universal accessibility, reflexivity, uniqueness, simplicity, intellect or
divinity is built in. Excluded middle enters as the explicit hypothesis
`TruthCore.Logic.ExcludedMiddle`, not as a Lean axiom.

`GroundAncestor` is Mathlib's `Relation.ReflTransGen` of `ActualConcreteGround`
(invariant 14), not a hand-rolled closure.
-/
namespace TruthCore.Causality.CogitoNecessaryConcrete

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete

variable {W B Episode : Type}

/-- `y` is an actual concrete ground of `x` at `w`: `y` is concrete, exists at
`w`, and grounds `x` at `w`. Abstract or absent grounds are excluded. -/
def ActualConcreteGround (m : Profile W B) (w : W) (y x : B) : Prop :=
  m.concrete y ∧ m.ontic.ExistsAt w y ∧ m.grounds w y x

/-- `x` is an actual concrete ground-ancestor of `b` at `w`: `x = b`, or a
finite chain of actual concrete grounds leads from `x` to `b`. -/
def GroundAncestor (m : Profile W B) (w : W) (x b : B) : Prop :=
  Relation.ReflTransGen (ActualConcreteGround m w) x b

/-- Thinker-local well-foundedness: every bearer of an occurring thought is
accessible for actual concrete grounding at `w`, so no infinite descending
chain of actual concrete grounds starts below it. Cycles or regresses through
non-concrete or absent grounds, and grounding elsewhere in the carrier, are
unconstrained. -/
def ThinkerGroundingAccessible (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∀ b e, Occurs e → Bears b e → Acc (ActualConcreteGround m w) b

/-- Thinker-local anti-brute-root principle: every actual concrete
ground-ancestor of a bearer of an occurring thought (the bearer included) that
is contingent at `w` has an actual concrete ground at `w`. It says nothing
about concreta outside the bearer's ancestry, and it does not say that the
bearer is contingent. -/
def ThinkerAncestryGrounded (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∀ b e x, Occurs e → Bears b e → GroundAncestor m w x b →
    m.concrete x → m.ontic.ExistsAt w x → ContingentAt m.ontic w x →
      ∃ y, ActualConcreteGround m w y x

/-- Some bearer of an occurring thought has an actual concrete
ground-ancestor (possibly itself) that exists at every world accessible
from `w`. De re, relative to the frame's accessibility. -/
def NecessaryConcreteAncestorOfThinker (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∃ b e x, Occurs e ∧ Bears b e ∧ GroundAncestor m w x b ∧
    m.concrete x ∧ m.ontic.ExistsAt w x ∧ NecessaryAt m.ontic w x

/-- Strengthening of the existing necessary-ancestor conclusion retaining the
actual-concrete-ground minimality used to select that same witness. This is
not global underivedness, nor absence of abstract or unmodelled support. -/
def NecessaryConcreteRootAncestorOfThinker (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∃ b e x, Occurs e ∧ Bears b e ∧ GroundAncestor m w x b ∧
    m.concrete x ∧ m.ontic.ExistsAt w x ∧ NecessaryAt m.ontic w x ∧
      ∀ y, ¬ ActualConcreteGround m w y x

/-- Some bearer of an occurring thought has an actual concrete
ground-ancestor (possibly itself) that is contingent at `w` and has no actual
concrete ground at `w`. A root of this relation only: it may still have an
abstract, non-concrete or otherwise unmodelled explanation. -/
def ContingentRootAncestorOfThinker (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  ∃ b e x, Occurs e ∧ Bears b e ∧ GroundAncestor m w x b ∧
    m.concrete x ∧ m.ontic.ExistsAt w x ∧ ContingentAt m.ontic w x ∧
      ∀ y, ¬ ActualConcreteGround m w y x

/-- The thinker-local fork: a necessary concrete ground-ancestor of some
bearer, or a contingent concrete root among some bearer's ground-ancestors. -/
def ThinkerAncestryRootFork (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W) : Prop :=
  NecessaryConcreteAncestorOfThinker m Occurs Bears w ∨
    ContingentRootAncestorOfThinker m Occurs Bears w

/-- The thinker-local conclusion gives the existing `NecessaryConcreteAt`. -/
theorem necessaryConcreteAt_of_ancestor {m : Profile W B} {Occurs : Episode → Prop}
    {Bears : B → Episode → Prop} {w : W}
    (h : NecessaryConcreteAncestorOfThinker m Occurs Bears w) :
    NecessaryConcreteAt m w := by
  obtain ⟨_, _, x, _, _, _, hc, he, hn⟩ := h
  exact ⟨x, hc, he, hn⟩

/-! ## Comparison with the global premises -/

/-- Each global premise implies its thinker-local counterpart, for every
profile, thought interpretation and world. -/
def GlobalPremisesImplyThinkerLocal : Prop :=
  ∀ (W B Episode : Type) (m : Profile W B) (Occurs : Episode → Prop)
    (Bears : B → Episode → Prop) (w : W),
    (WellFounded (m.grounds w) → ThinkerGroundingAccessible m Occurs Bears w) ∧
      (EveryContingentGroundedAt m w → ThinkerAncestryGrounded m Occurs Bears w)

/-- Four rigid candidates: a thinker, two mutually grounding beings and an
ungrounded one. -/
inductive Cand where
  | thinker
  | left
  | right
  | brute

/-- The thinker exists at both worlds; the other three only at `true`. -/
def candExists : Bool → Cand → Prop
  | _, .thinker => True
  | w, .left => w = true
  | w, .right => w = true
  | w, .brute => w = true

/-- `left` and `right` ground each other at every world; nothing else grounds.
Every case is listed (no wildcard), so that case analysis needs no `propext`. -/
def candGrounds (_ : Bool) : Cand → Cand → Prop
  | .thinker, .thinker => False
  | .thinker, .left => False
  | .thinker, .right => False
  | .thinker, .brute => False
  | .left, .thinker => False
  | .left, .left => False
  | .left, .right => True
  | .left, .brute => False
  | .right, .thinker => False
  | .right, .left => True
  | .right, .right => False
  | .right, .brute => False
  | .brute, .thinker => False
  | .brute, .left => False
  | .brute, .right => False
  | .brute, .brute => False

/-- The strictness model: two worlds, universal accessibility, every candidate
concrete, existence and grounding as above. -/
def strictProfile : Profile Bool Cand where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := candExists
    Causes := candGrounds
  }
  concrete := fun _ => True
  grounds := candGrounds

/-- One occurring thought, borne by the thinker only. -/
def strictBears : Cand → Unit → Prop
  | .thinker, _ => True
  | .left, _ => False
  | .right, _ => False
  | .brute, _ => False

/-- At `true`: all six non-logical premises of the necessary-ancestor theorem
hold (so they are jointly satisfiable) together with its conclusion; the
thinker exists at every accessible world and is not contingent; and both global
premises fail: grounding is not well-founded (the `left`/`right` cycle) and an
actual contingent concretum (`brute`) has no actual concrete ground. -/
def StrictlyWeakerModel : Prop :=
  ThoughtOccurs (fun _ : Unit => True) ∧
    EveryThoughtHasSubject (fun _ : Unit => True) strictBears ∧
    EveryBearerIsConcrete (fun _ : Unit => True) strictBears strictProfile.concrete ∧
    EveryBearerExistsAt strictProfile.ontic (fun _ : Unit => True) strictBears true ∧
    ThinkerGroundingAccessible strictProfile (fun _ : Unit => True) strictBears true ∧
    ThinkerAncestryGrounded strictProfile (fun _ : Unit => True) strictBears true ∧
    NecessaryConcreteAncestorOfThinker strictProfile (fun _ : Unit => True) strictBears true ∧
    NecessaryAt strictProfile.ontic true Cand.thinker ∧
    ¬ ContingentAt strictProfile.ontic true Cand.thinker ∧
    ¬ WellFounded (strictProfile.grounds true) ∧
    ¬ EveryContingentGroundedAt strictProfile true

/-! ## Omission controls for the necessary-ancestor conclusion -/

/-- A one-world, one-candidate profile with the supplied existence and
concreteness and no grounding. -/
def unitProfile (ex conc : Prop) : Profile Unit Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => ex
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => conc
  grounds := fun _ _ _ => False

/-- O omitted: no thought occurs; the other five premises hold vacuously and
no necessary concrete ancestor of a thinker exists. -/
def NoThoughtAncestryControl : Prop :=
  ∃ (m : Profile Unit Unit) (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ¬ ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears m.concrete ∧
      EveryBearerExistsAt m.ontic Occurs Bears () ∧
      ThinkerGroundingAccessible m Occurs Bears () ∧
      ThinkerAncestryGrounded m Occurs Bears () ∧
      ¬ NecessaryConcreteAncestorOfThinker m Occurs Bears ()

/-- B omitted: a thought occurs without a bearer. -/
def BearerlessAncestryControl : Prop :=
  ∃ (m : Profile Unit Unit) (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears m.concrete ∧
      EveryBearerExistsAt m.ontic Occurs Bears () ∧
      ThinkerGroundingAccessible m Occurs Bears () ∧
      ThinkerAncestryGrounded m Occurs Bears () ∧
      ¬ NecessaryConcreteAncestorOfThinker m Occurs Bears ()

/-- C omitted: the bearer exists at every world but is not concrete. -/
def NonConcreteBearerAncestryControl : Prop :=
  ∃ (m : Profile Unit Unit) (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      ¬ EveryBearerIsConcrete Occurs Bears m.concrete ∧
      EveryBearerExistsAt m.ontic Occurs Bears () ∧
      ThinkerGroundingAccessible m Occurs Bears () ∧
      ThinkerAncestryGrounded m Occurs Bears () ∧
      ¬ NecessaryConcreteAncestorOfThinker m Occurs Bears ()

/-- E omitted: the bearer is concrete but exists at no world. -/
def NonexistentBearerAncestryControl : Prop :=
  ∃ (m : Profile Unit Unit) (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      EveryBearerIsConcrete Occurs Bears m.concrete ∧
      ¬ EveryBearerExistsAt m.ontic Occurs Bears () ∧
      ThinkerGroundingAccessible m Occurs Bears () ∧
      ThinkerAncestryGrounded m Occurs Bears () ∧
      ¬ NecessaryConcreteAncestorOfThinker m Occurs Bears ()

/-- Two candidates that exist only at `true` and ground each other. -/
def cycleProfile : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => w = true
    Causes := fun _ y x => y ≠ x
  }
  concrete := fun _ => True
  grounds := fun _ y x => y ≠ x

/-- Local well-foundedness omitted: the thinker (`true`) and its only other
candidate ground each other, both contingent. Every contingent ancestor is
grounded, yet no ancestor is necessary. -/
def CyclicThinkerAncestryControl : Prop :=
  ThoughtOccurs (fun _ : Unit => True) ∧
    EveryThoughtHasSubject (fun _ : Unit => True) (fun b (_ : Unit) => b = true) ∧
    EveryBearerIsConcrete (fun _ : Unit => True) (fun b (_ : Unit) => b = true)
      cycleProfile.concrete ∧
    EveryBearerExistsAt cycleProfile.ontic (fun _ : Unit => True)
      (fun b (_ : Unit) => b = true) true ∧
    ¬ ThinkerGroundingAccessible cycleProfile (fun _ : Unit => True)
      (fun b (_ : Unit) => b = true) true ∧
    ThinkerAncestryGrounded cycleProfile (fun _ : Unit => True)
      (fun b (_ : Unit) => b = true) true ∧
    ¬ NecessaryConcreteAncestorOfThinker cycleProfile (fun _ : Unit => True)
      (fun b (_ : Unit) => b = true) true

/-- One candidate, existing only at `true`, with no grounds. -/
def bruteProfile : Profile Bool Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => w = true
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Local anti-brute-root omitted: a contingent thinker with no ground at all.
Its ancestry is trivially well-founded, and no ancestor is necessary. This is
the issue's "underived contingent thinker": underived is not necessary. -/
def BruteThinkerAncestryControl : Prop :=
  ThoughtOccurs (fun _ : Unit => True) ∧
    EveryThoughtHasSubject (fun _ : Unit => True) (fun (_ : Unit) (_ : Unit) => True) ∧
    EveryBearerIsConcrete (fun _ : Unit => True) (fun (_ : Unit) (_ : Unit) => True)
      bruteProfile.concrete ∧
    EveryBearerExistsAt bruteProfile.ontic (fun _ : Unit => True)
      (fun (_ : Unit) (_ : Unit) => True) true ∧
    ThinkerGroundingAccessible bruteProfile (fun _ : Unit => True)
      (fun (_ : Unit) (_ : Unit) => True) true ∧
    ¬ ThinkerAncestryGrounded bruteProfile (fun _ : Unit => True)
      (fun (_ : Unit) (_ : Unit) => True) true ∧
    ¬ NecessaryConcreteAncestorOfThinker bruteProfile (fun _ : Unit => True)
      (fun (_ : Unit) (_ : Unit) => True) true

/-- The comparison and control bundle: the global premises imply the local
ones; one model shows the converse fails (with a necessary, non-contingent
thinker); and each of the six non-logical premises of the necessary-ancestor
theorem is needed. -/
def CogitoAncestryControls : Prop :=
  GlobalPremisesImplyThinkerLocal ∧ StrictlyWeakerModel ∧
    NoThoughtAncestryControl ∧ BearerlessAncestryControl ∧
    NonConcreteBearerAncestryControl ∧ NonexistentBearerAncestryControl ∧
    CyclicThinkerAncestryControl ∧ BruteThinkerAncestryControl

end TruthCore.Causality.CogitoNecessaryConcrete
