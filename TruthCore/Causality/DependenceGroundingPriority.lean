module

public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Causality.EsseCausePriority

/-! Existential dependence to simple priority through actual grounding (#1590)

Analyst formulations, attribution deferred. The issue's route is

`ActualConcrete w c ∧ ActualConcrete w x ∧ DependsForBeing x c`
→ `grounds w c x` → `PriorSimply c x`,

with the dependence-to-grounding step taken in its **distinct-relata** version
`ReflexiveDependenceScope.ActualDistinctDependenceIsGrounding` (#1593), not the
unrestricted `Round2Grounding.ActualDependenceIsGrounding`, and the second step
the existing OPEN bridge `Round2Grounding.ActualGroundingIsSimplePriority`.
Nothing here is new primitive vocabulary:

* `ActualDistinctDependencePriority`: if an actual concretum `x` depends for its
  being on a distinct actual concretum `c`, then `c` is simply prior to `x`.
  It is the actual-concrete, distinct-relata counterpart of
  `CausalMapsBatch1.NonmutualDependenceSufficesForPriority`. It needs no
  nonmutuality antecedent and no possible-separation (`CanBeWithout`) premise;
  it does not give the unscoped premise, which also covers non-actual and
  non-concrete relata.
* `NoActualConcretumAt`: nothing is an actual concretum at `w`. It is the
  conclusion of the checked incompatibility recorded below: reflexive
  dependence, the *unrestricted* dependence-to-grounding bridge, actual grounding
  as simple priority and priority requiring nonmutual dependence jointly exclude
  every actual concretum. The distinct-relata bundle has a model with reflexive
  dependence and an actual concretum (`Control.ReflexiveCompatible`).

`DependsForBeing` is DEF-DEPENDS-FOR-BEING (DEPENDENCE_FOR_BEING_VERSUS_STRICT_GROUND_1);
`grounds w` is the profile's selected relation (the actual concrete grounding
edge, a1b2e330); `PriorSimply` is the primitive SIMPLY_PRIOR_1. No identity of
the three relations is assumed; each passage is an OPEN one-directional bridge.
-/

@[expose] public section

namespace TruthCore.Causality.DependenceGroundingPriority

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)

variable {W B : Type}

/-- If an actual concretum `x` depends for its being on an actual concretum `c`
distinct from it, then `c` is simply prior to `x`. Silent on `D x x`, on
non-actual or non-concrete relata, and on respects of priority. -/
def ActualDistinctDependencePriority (m : Profile W B) (w : W)
    (DependsForBeing PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → ActualConcrete m w x → ActualConcrete m w c →
    DependsForBeing x c → PriorSimply c x

/-- The restriction of `NonmutualDependenceSufficesForPriority` to actual
concreta at `w`. Recorded only as the target of a checked corollary (the
nonmutuality antecedent yields distinctness); not a corpus statement. -/
def ActualNonmutualDependencePriority (m : Profile W B) (w : W)
    (DependsForBeing PriorSimply : B → B → Prop) : Prop :=
  ∀ y x, ActualConcrete m w x → ActualConcrete m w y →
    DependsForBeing x y → ¬ DependsForBeing y x → PriorSimply y x

/-- Nothing is an actual concretum (concrete and existing) at `w`. -/
def NoActualConcretumAt (m : Profile W B) (w : W) : Prop :=
  ∀ a, ¬ ActualConcrete m w a

/-! ## Controls

`Bool` worlds and beings, reading world `true`, built with
`Round2Grounding.Control.mk`. Satisfiability and omission only; no model is
claimed to describe reality. -/

namespace Control

open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority
  ActualDependenceIsGrounding)
open TruthCore.Causality.ReflexiveDependenceScope (ActualDistinctDependenceIsGrounding
  DependenceForBeingReflexive)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)

/-- Everything exists everywhere and is concrete; nothing is grounded. -/
abbrev bare : Profile Bool Bool := TruthCore.Causality.EsseCausePriority.Control.bare
/-- As `bare`, but `true` grounds `false` at `true`. -/
abbrev grounded : Profile Bool Bool := TruthCore.Causality.EsseCausePriority.Control.grounded
/-- Reflexive dependence with one distinct edge: `false` depends on `true`. -/
abbrev dep (x y : Bool) : Prop := x = y ∨ (x = false ∧ y = true)
/-- `true` is simply prior to `false`. -/
abbrev prior (y x : Bool) : Prop := y = true ∧ x = false
/-- Nothing is simply prior to anything. -/
abbrev noPrior (_ _ : Bool) : Prop := False

/-- Joint witness, with reflexive dependence: the distinct-relata bridge, the
grounding-to-priority bridge and priority-requires-nonmutual-dependence hold
together; `false` and `true` are actual concreta, `false` depends on `true`, and
`true` is prior to `false`. -/
def ReflexiveCompatible : Prop :=
  DependenceForBeingReflexive dep ∧
  ActualDistinctDependenceIsGrounding grounded true dep ∧
  ActualGroundingIsSimplePriority grounded true prior ∧
  PriorityRequiresNonmutualDependence prior dep ∧
  ActualConcrete grounded true false ∧ ActualConcrete grounded true true ∧
  dep false true ∧ prior true false

/-- On the same profile and dependence, the unrestricted bridge fails: `true`
depends on itself but does not ground itself. -/
def UnrestrictedFails : Prop :=
  ¬ ActualDependenceIsGrounding grounded true dep

/-- Omitting the distinct-relata bridge: grounding-to-priority holds (vacuously:
nothing grounds), a distinct dependence edge joins two actual concreta, and the
scoped priority fails. -/
def OmitDistinctGround : Prop :=
  ActualGroundingIsSimplePriority bare true noPrior ∧
  ¬ ActualDistinctDependencePriority bare true dep noPrior

/-- Omitting the grounding-to-priority bridge: the distinct-relata bridge holds,
nothing is simply prior, and the scoped priority fails. -/
def OmitGroundingPriority : Prop :=
  ActualDistinctDependenceIsGrounding grounded true dep ∧
  ¬ ActualDistinctDependencePriority grounded true dep noPrior

/-- The controls of this module. -/
def Certificate : Prop :=
  ReflexiveCompatible ∧ UnrestrictedFails ∧ OmitDistinctGround ∧ OmitGroundingPriority

end Control

end TruthCore.Causality.DependenceGroundingPriority
