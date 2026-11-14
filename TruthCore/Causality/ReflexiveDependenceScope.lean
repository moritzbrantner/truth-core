module

public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Causality.DependenceStrictGroundMapStrength

/-! Reflexive existence-requirement versus strict dependence for being (#1593)

Analyst formulations, attribution deferred. `DependsForBeing x y`
(DEF-DEPENDS-FOR-BEING, written `D x y`: `x` depends for its being on `y`) is a
primitive parameter with no built-in self-relation law. Two root-adjacent
premises read it differently on the diagonal:

* `DistinctBeingsNotMutuallyDependent D` (STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT)
  says nothing about `D x x`;
* `DependenceForBeingAsymmetric D` (STMT-DEPENDENCE-FOR-BEING-ASYMMETRIC)
  excludes `D x x`.

They conflict only on a reading under which `D` is reflexive. Read literally as
a counterfactual, "`x` would not be if `x` were not" is an instance of the
counterfactual identity law, so the literal reading of the definition makes `D`
reflexive. That reflexivity is the separate OPEN statement
`DependenceForBeingReflexive`; nothing here builds it into `D`.

The structural laws below are stated separately, so that each result shows
which of them it uses: reflexivity, transitivity, and antisymmetry (on distinct
beings, `DistinctBeingsNotMutuallyDependent`). The strict, self-excluding part
of `D` reuses `DistinctEdge` of `DependenceStrictGroundMapStrength`; no new
primitive or sense is introduced. -/

@[expose] public section

namespace TruthCore.Causality.ReflexiveDependenceScope

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2PerfectionPrimacy (DistinctBeingsNotMutuallyDependent)
open TruthCore.Causality.CausalMapsBatch1
  (NonmutualDependenceSufficesForPriority PriorityRequiresNonmutualDependence)
open TruthCore.Causality.DependenceStrictGroundMapStrength (DistinctEdge)

variable {W B : Type}

/-- Everything depends for its being on itself: the non-strict, existence-
requirement reading of `D`, on which "`x` would not be if `x` were not" holds
trivially. OPEN; it is not part of DEF-DEPENDS-FOR-BEING. -/
def DependenceForBeingReflexive (D : B → B → Prop) : Prop :=
  ∀ x, D x x

/-- Dependence for being is transitive: what depends on something that depends
on `z` depends on `z`. OPEN; a direct productive edge need not have it. -/
def DependenceForBeingTransitive (D : B → B → Prop) : Prop :=
  ∀ x y z, D x y → D y z → D x z

/-- On any domain with at least one being, dependence for being is not
asymmetric. -/
def InhabitedDependenceNotAsymmetric (D : B → B → Prop) : Prop :=
  Nonempty B → ¬ DependenceForBeingAsymmetric D

/-- No actual concretum grounds itself under the selected relation at `w`. -/
def ActualGroundingIrreflexive (m : Profile W B) (w : W) : Prop :=
  ∀ a, ActualConcrete m w a → ¬ m.grounds w a a

/-- Every actual concretum grounds itself under the selected relation at `w`. -/
def EveryActualConcretumGroundsItself (m : Profile W B) (w : W) : Prop :=
  ∀ a, ActualConcrete m w a → m.grounds w a a

/-- The distinct-relata restriction of `ActualDependenceIsGrounding`: if an
actual concretum `x` depends for its being on a *different* actual concretum
`c`, then `c` grounds `x` at `w`. Silent on `D x x`. -/
def ActualDistinctDependenceIsGrounding (m : Profile W B) (w : W)
    (D : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → ActualConcrete m w x → ActualConcrete m w c → D x c → m.grounds w c x

/-- Nonmutuality on distinct beings is exactly asymmetry of the strict
(distinct-step) part of `D`. -/
theorem distinctNonmutual_iff_distinctEdge_asymmetric (D : B → B → Prop) :
    DistinctBeingsNotMutuallyDependent D ↔
      DependenceForBeingAsymmetric (DistinctEdge D) := by
  constructor
  · intro h x y hxy hyx
    exact h x y hxy.1 hxy.2 hyx.2
  · intro h x y hne hxy hyx
    exact h x y ⟨hne, hxy⟩ ⟨fun e => hne e.symm, hyx⟩

/-- Under reflexivity and distinct nonmutuality, the strict part
`D x y ∧ ¬ D y x` that the two priority bridges pair with simple priority is
exactly the distinct-step part `x ≠ y ∧ D x y`. -/
theorem strictPart_iff_distinctEdge (D : B → B → Prop)
    (hRefl : DependenceForBeingReflexive D)
    (hDistinct : DistinctBeingsNotMutuallyDependent D) (x y : B) :
    (D x y ∧ ¬ D y x) ↔ DistinctEdge D x y := by
  constructor
  · rintro ⟨hxy, hyx⟩
    exact ⟨fun e => by subst e; exact hyx (hRefl x), hxy⟩
  · rintro ⟨hne, hxy⟩
    exact ⟨hxy, hDistinct x y hne hxy⟩

/-- Under the two OPEN priority bridges, simple priority is the strict part of
`D`: `PriorSimply y x ↔ D x y ∧ ¬ D y x`. -/
theorem priority_iff_strictPart (PriorSimply D : B → B → Prop)
    (hSuff : NonmutualDependenceSufficesForPriority PriorSimply D)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D) (y x : B) :
    PriorSimply y x ↔ (D x y ∧ ¬ D y x) :=
  ⟨hReq y x, fun h => hSuff y x h.1 h.2⟩

namespace Control

/-- The issue's identity control and an order control on two beings. With
`D x y := x = y`, `D` is reflexive and nonmutual on distinct beings but not
asymmetric. With `D x y := x = y ∨ (x = true ∧ y = false)` on `Bool` (`true`
depends on `false`), `D` is moreover transitive and has a distinct edge, and it
is still not asymmetric. Formal interpretations only: they separate the
premises' meanings; they say nothing about which beings depend on which. -/
def ReflexiveDistinctSeparation : Prop :=
  (DependenceForBeingReflexive (fun x y : Bool => x = y) ∧
      DistinctBeingsNotMutuallyDependent (fun x y : Bool => x = y) ∧
      ¬ DependenceForBeingAsymmetric (fun x y : Bool => x = y)) ∧
    (DependenceForBeingReflexive (fun x y : Bool => x = y ∨ (x = true ∧ y = false)) ∧
      DependenceForBeingTransitive (fun x y : Bool => x = y ∨ (x = true ∧ y = false)) ∧
      DistinctBeingsNotMutuallyDependent
        (fun x y : Bool => x = y ∨ (x = true ∧ y = false)) ∧
      DistinctEdge (fun x y : Bool => x = y ∨ (x = true ∧ y = false)) true false ∧
      ¬ DependenceForBeingAsymmetric (fun x y : Bool => x = y ∨ (x = true ∧ y = false)))

/-- Direct edge on `Fin 3`: reflexive, plus the direct steps `2 → 1` and
`1 → 0` (`2` depends on `1`, `1` depends on `0`), but not `2 → 0`. -/
def chainD (x y : Fin 3) : Prop :=
  x = y ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

/-- Strict part of `chainD`, used as simple priority: `y` is prior to `x` iff
`x` depends on `y` and not conversely. -/
def chainPrior (y x : Fin 3) : Prop :=
  chainD x y ∧ ¬ chainD y x

/-- Reflexive, transitive dependence with one reciprocal pair (`0` and `1`
depend on each other). -/
def pairD (_x _y : Fin 2) : Prop := True

/-- Order-law controls. (1) The direct-edge chain satisfies reflexivity,
distinct nonmutuality and both priority bridges for its strict part, yet `D` is
not transitive and neither is the priority it induces: transitivity of priority
needs transitivity of `D` (or of its closure), not the bridges. (2) The
reciprocal pair is reflexive and transitive but violates distinct
nonmutuality, and its strict part is empty, so the bridges then give no
priority between the pair. Formal interpretations only. -/
def OrderLawControls : Prop :=
  (DependenceForBeingReflexive chainD ∧
      DistinctBeingsNotMutuallyDependent chainD ∧
      NonmutualDependenceSufficesForPriority chainPrior chainD ∧
      PriorityRequiresNonmutualDependence chainPrior chainD ∧
      ¬ DependenceForBeingTransitive chainD ∧
      ¬ (∀ x y z, chainPrior x y → chainPrior y z → chainPrior x z)) ∧
    (DependenceForBeingReflexive pairD ∧ DependenceForBeingTransitive pairD ∧
      ¬ DistinctBeingsNotMutuallyDependent pairD ∧
      ∀ x y : Fin 2, ¬ (pairD x y ∧ ¬ pairD y x))

end Control

end TruthCore.Causality.ReflexiveDependenceScope
