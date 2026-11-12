module

public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Causality.SpineRivalsRootEsse
public import TruthCore.Causality.UnderivedRootRoute

/-!
# Well-founded necessary support (J2) and the mutual-support rival

Analyst formulations, attribution deferred. Target: premise J2 of the modal
spine's join, `ConcreteNecessaryUnionWF` (`STMT-CONCRETE-NECESSARY-UNION-WF`),
consumed by `NecessaryConcreteUnderived.checks` toward
`STMT-NECESSARY-CONCRETE-UNDERIVED-AT`, and its recorded rival
`SpineRivalsRootEsse.NecessaryConcretaMutualSupport`.

"Support of being" is the profile's selected relation `grounds v a b`: at world
`v`, `b`'s existence there is sustained by `a` (a flame by its fuel, a song by
its singing), not `a`'s having once produced `b` (parents and child). No
transitivity or cross-world behaviour of the relation is assumed; that is what
the premises below state, explicitly and open.

Two conditions are introduced:

* `NecessarySupportActuallyCovered`: whatever necessary concretum has its being
  supported by an existing concretum at some admitted world has its being
  supported by some concretum existing at the selected world. Motivation (open,
  not established): having one's being supported is a standing feature of a
  dependent mode of being, not an optional extra a self-standing necessary being
  could receive elsewhere. It does not require the same supporter, invariance of
  edges, or necessity of supporters. It is a weakening, on concrete supporters
  and targets, of the existing open premise
  `UnderivedRootRoute.NecessarySupportIsPresent`, which demands that the very
  supporter found elsewhere exist and support at the selected world.
* `NoNecessaryConcretaMutualSupport`: the negation of the recorded rival.

Two candidate discriminators are tested only in models:
`EveryWorldGroundingWF` (each world's own present support is well-founded) and
the negation of the rival (no reversed pair of support edges among necessary
concreta, even across worlds). The `Control` models show neither yields J2 or the
join's endpoint.

The stronger one-way invariance premise `NoNovelNecessarySupport` (existing
`STMT-NO-NOVEL-NECESSARY-SUPPORT`, instantiated on the concrete subtype) is
reused, not restated.
-/

@[expose] public section

namespace TruthCore.Causality.NecessarySupportCoverage

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.SpineRivalsRootEsse
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- Whatever concretum necessary at `w` has its being supported by an existing
concretum at some admitted world `v` has its being supported by some concretum
existing at `w`, under the selected relation at `w`. The supporter at `w` need not
be the supporter at `v`, nor necessary; no edge need persist between worlds. -/
def NecessarySupportActuallyCovered (m : Profile W B) (w : W) : Prop :=
  ∀ v a b, m.concrete a → m.concrete b → NecessaryAt m.ontic w b →
    m.ontic.ExistsAt v a → m.grounds v a b →
      ∃ c, m.concrete c ∧ m.ontic.ExistsAt w c ∧ m.grounds w c b

/-- No two concreta necessary at `w` support each other, each at some admitted
world: the negation of the recorded rival `NecessaryConcretaMutualSupport`.
Equivalently, among necessary concreta no support edge is ever reversed, even
across worlds; the pair may coincide, so self-support is excluded too. -/
def NoNecessaryConcretaMutualSupport (m : Profile W B) (w : W) : Prop :=
  ¬ NecessaryConcretaMutualSupport m w

/-- Candidate discriminator tested in the controls: at every world, the selected
relation restricted to concreta existing there is well-founded. -/
def EveryWorldGroundingWF (m : Profile W B) : Prop :=
  ∀ v, ActualGroundingWF m v

namespace Control

/-- Three labels for worlds or candidates. A plain enumeration rather than
`Fin 3`, so the certificates need no `Fin` arithmetic or decidability library
lemmas (Comparator checks the same library constants in Challenge and Solution). -/
inductive Tri where
  | t0 | t1 | t2

/-- Three worlds and three concreta, all existing everywhere, universal access.
At world `tᵢ`, `tᵢ` supports `tᵢ₊₁` (mod 3): support rotates around a triangle. -/
def rotatingTriangle : Profile Tri Tri where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests cross-world support, not the concrete/abstract line)
  grounds := fun v a b =>
    (v = .t0 ∧ a = .t0 ∧ b = .t1) ∨ (v = .t1 ∧ a = .t1 ∧ b = .t2) ∨
      (v = .t2 ∧ a = .t2 ∧ b = .t0)

/-- The rotating triangle: no reversed pair and well-founded support at every
world, with every other premise of `NecessaryConcreteUnderived.checks`; yet the
union is not well-founded, no necessary concretum is underived at every admitted
world, and coverage fails. -/
def RotatingTriangleSurvives : Prop :=
  NoNecessaryConcretaMutualSupport rotatingTriangle .t0 ∧
    EveryWorldGroundingWF rotatingTriangle ∧
    InhabitedConcreteAt rotatingTriangle.ontic rotatingTriangle.concrete .t0 ∧
    ActualGroundingWF rotatingTriangle .t0 ∧
    EveryContingentGroundedAt rotatingTriangle .t0 ∧
    ActualReflexive rotatingTriangle.ontic .t0 ∧
    NoContingentConcreteSupport rotatingTriangle .t0 ∧ ExcludedMiddle ∧
    ¬ ConcreteNecessaryUnionWF rotatingTriangle .t0 ∧
    ¬ NecessaryConcreteUnderivedAt rotatingTriangle .t0 ∧
    ¬ NecessarySupportActuallyCovered rotatingTriangle .t0

/-- Two worlds, three concreta `t0` (root), `t1`, `t2`, all existing everywhere.
At `false`: `t0 → t1` and `t1 → t2`; at `true`: `t0 → t2` and `t2 → t1`. -/
def rootedPair : Profile Bool Tri where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests cross-world support, not the concrete/abstract line)
  grounds := fun v a b =>
    (v = false ∧ ((a = .t0 ∧ b = .t1) ∨ (a = .t1 ∧ b = .t2))) ∨
      (v = true ∧ ((a = .t0 ∧ b = .t2) ∨ (a = .t2 ∧ b = .t1)))

/-- The rooted pair: the mutual-support rival holds with every other premise of
`NecessaryConcreteUnderived.checks` and with coverage; the union is not
well-founded, and both the one-way no-novel-edge condition and the stronger
same-supporter presence condition fail; and yet the join's endpoint holds (the
root `t0` is underived at every admitted world). -/
def RootedPairCompatible : Prop :=
  NecessaryConcretaMutualSupport rootedPair false ∧
    EveryWorldGroundingWF rootedPair ∧
    InhabitedConcreteAt rootedPair.ontic rootedPair.concrete false ∧
    ActualGroundingWF rootedPair false ∧
    EveryContingentGroundedAt rootedPair false ∧
    ActualReflexive rootedPair.ontic false ∧
    NoContingentConcreteSupport rootedPair false ∧
    NecessarySupportActuallyCovered rootedPair false ∧ ExcludedMiddle ∧
    ¬ ConcreteNecessaryUnionWF rootedPair false ∧
    ¬ NoNovelNecessarySupport (concreteOntic rootedPair) (concreteSupport rootedPair) false ∧
    ¬ TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent rootedPair false ∧
    NecessaryConcreteUnderivedAt rootedPair false

/-- Two worlds, two concreta existing everywhere; only at `true` does `false`
support `true`. -/
def uncoveredEdge : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests cross-world support, not the concrete/abstract line)
  grounds := fun v a b => v = true ∧ a = false ∧ b = true

/-- The uncovered edge: every premise of `NecessaryConcreteUnderived.checks`
(including J1 and J2) and its endpoint hold while coverage and the one-way
no-novel-edge condition fail. -/
def UncoveredEdgeControl : Prop :=
  InhabitedConcreteAt uncoveredEdge.ontic uncoveredEdge.concrete false ∧
    ActualGroundingWF uncoveredEdge false ∧
    EveryContingentGroundedAt uncoveredEdge false ∧
    ActualReflexive uncoveredEdge.ontic false ∧
    NoContingentConcreteSupport uncoveredEdge false ∧
    ConcreteNecessaryUnionWF uncoveredEdge false ∧ ExcludedMiddle ∧
    ¬ NecessarySupportActuallyCovered uncoveredEdge false ∧
    ¬ NoNovelNecessarySupport (concreteOntic uncoveredEdge) (concreteSupport uncoveredEdge) false ∧
    NecessaryConcreteUnderivedAt uncoveredEdge false

/-- All three controls. -/
def Controls : Prop :=
  RotatingTriangleSurvives ∧ RootedPairCompatible ∧ UncoveredEdgeControl

end Control

end TruthCore.Causality.NecessarySupportCoverage
