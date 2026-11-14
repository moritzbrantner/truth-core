module

public import Mathlib.Logic.Relation
public import TruthCore.Causality.DependenceStrictGroundMap

@[expose] public section

namespace TruthCore.Causality.DependenceStrictGroundMapStrength

open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Causality.DependenceStrictGroundMap

/-- A dependence edge between two *distinct* beings, oriented from the
dependent `x` to the being `y` it depends on. Self-edges are dropped, as in
`DependenceMapsToStrictExistenceGround`. -/
def DistinctEdge {B : Type} (D : B → B → Prop) (x y : B) : Prop :=
  x ≠ y ∧ D x y

/-- Structural acyclicity of distinct-step dependence: no finite chain of
`DistinctEdge D` steps (Mathlib `Relation.TransGen`) returns to its start.
This is a property of the relation `D` alone. It is strictly stronger than
`DistinctBeingsNotMutuallyDependent D`, which excludes only two-step cycles,
and it says nothing about infinite descent or well-foundedness. -/
def DistinctDependenceAcyclic {B : Type} (D : B → B → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen (DistinctEdge D) x x

namespace Control

/-- Nonvacuity of the strict-ground support bundle: one consistent PLG
theory over `Nat`, the identity labelling and a dependence relation with a
distinct edge (`D x y` iff `y = x + 1`) jointly satisfy consistency and the
dependence-to-strict-ground map. A formal interpretation only; it says
nothing about which beings or existence facts there are. -/
def Nonvacuous : Prop :=
  ∃ (S : Set (Sequent Nat)) (D : Nat → Nat → Prop),
    Consistent S ∧ DependenceMapsToStrictExistenceGround D id S ∧
    ∃ x y, x ≠ y ∧ D x y

end Control

end TruthCore.Causality.DependenceStrictGroundMapStrength
