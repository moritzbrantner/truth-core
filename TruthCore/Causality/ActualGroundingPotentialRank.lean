module

public import TruthCore.Causality.Round3CogitoBase
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Analyst quantitative framework, attribution deferred. The supplied scalar
potential is a coordinate on rigid candidate beings, not integer time, entropy,
power, explanatory adequacy or a definition of grounding. Its lower bound and
uniform edge gap are OPEN calibration constraints on the unchanged relation.
They concern one world and actual concreta only. No applicability to reality,
converse, finite cardinality, temporal duration or cross-world union is claimed.
A rank 0,1,2 on a three-node grounding chain is a mathematical example; reverse
successor grounding on Nat supplies the omission controls. Real examples remain
unavailable without an independently supplied calibration bridge. -/

@[expose] public section

namespace TruthCore.Causality.ActualGroundingPotentialRank
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.Round3CogitoBase (ActualGroundingFiniteRank)

/-- OPEN: one lower bound for the potential of ALL actual concreta at w. -/
def PotentialLowerBound {W B : Type} (m : Profile W B) (w : W)
    (S : B → ℝ) (L : ℝ) : Prop :=
  ∀ x, ActualConcrete m w x → L ≤ S x

/-- OPEN: one strictly positive real gap, fixed across every selected edge. -/
def PositiveGap (ε : ℝ) : Prop := 0 < ε

/-- OPEN correlation, not the meaning of grounding. Both endpoints are actual
concreta at the SAME world; y grounds x, and potential increases toward x.
Pointwise positive varying gaps are insufficient for this uniform profile. -/
def UniformGroundGap {W B : Type} (m : Profile W B) (w : W)
    (S : B → ℝ) (ε : ℝ) : Prop :=
  ∀ x y, ActualConcrete m w x → ActualConcreteGround m w y x → S y + ε ≤ S x

/-- Explicit rival: no Nat rank for the same selected-world actual relation.
This allows nonfoundation OR a well-founded hierarchy of transfinite height. -/
def ActualGroundingUnranked {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ¬ ActualGroundingFiniteRank m w

namespace Control
/-- Fixed carrier, actual/concrete predicates and predecessor orientation for
all omission models. Every n has the actual concrete ground n+1. -/
def descending : Profile Unit Nat where
  ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ y x => y = x + 1

/-- A nonempty chain with genuine edges; finite rank does not bound cardinality. -/
def ascending : Profile Unit Nat where
  ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ y x => x = y + 1

/-- A bounded potential with strictly positive but nonuniform edge gaps. -/
noncomputable def varying (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)

/-- Same descending graph in each conjunct: omit positivity (epsilon=0),
lower bound (S n=-n), or edge gap (constant S). Each retains the other two.
The common graph is neither Nat-ranked nor well-founded. The final ascending
Nat witness has a genuine edge and all three assumptions simultaneously. -/
def Certificate : Prop :=
  (PotentialLowerBound descending () (fun _ => 0) 0 ∧
   UniformGroundGap descending () (fun _ => 0) 0 ∧ ¬ PositiveGap 0) ∧
  (PositiveGap 1 ∧ UniformGroundGap descending () (fun n => -(n : ℝ)) 1 ∧
   ¬ ∃ L, PotentialLowerBound descending () (fun n => -(n : ℝ)) L) ∧
  (PositiveGap 1 ∧ PotentialLowerBound descending () (fun _ => 0) 0 ∧
   ¬ UniformGroundGap descending () (fun _ => 0) 1) ∧
  (¬ ActualGroundingFiniteRank descending () ∧ ¬ ActualGroundingWF descending ()) ∧
  (PotentialLowerBound descending () varying 0 ∧
   (∀ x y, ActualConcrete descending () x → ActualConcreteGround descending () y x →
     varying y < varying x) ∧
   ∀ ε, PositiveGap ε → ¬ UniformGroundGap descending () varying ε) ∧
  (PositiveGap 1 ∧ PotentialLowerBound ascending () (fun n => (n : ℝ)) 0 ∧
   UniformGroundGap ascending () (fun n => (n : ℝ)) 1 ∧
   ActualConcreteGround ascending () 0 1 ∧ ActualGroundingFiniteRank ascending ())
end Control
end TruthCore.Causality.ActualGroundingPotentialRank
