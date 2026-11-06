module

public import TruthCore.Mereology.SumOneComplementation
public import TruthCore.Causality.AtomisticCausalSource
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Data.Fintype.Powerset

/-! Analyst formulations for #1062; attribution deferred. The same common-part
overlap, exact remainder and all-nonempty-family fusion semantics are used by
both models. A regular open region is Mathlib's Heyting-regular open set, not
a new surrogate notion. Inclusion interprets parthood in this mathematical
model; applicability to actual material objects remains OPEN.
-/

@[expose] public section

namespace TruthCore.Mereology.AtomlessFusionProfile

open UniversalFusionBoundary SumOneComplementation

/-- Nonzero elements; excluding Boolean zero is distinct from proving there is
no least remaining object, which is checked separately in the concrete models. -/
abbrev Positive (A : Type) [Bot A] := {x : A // x ≠ ⊥}

/-- The unchanged full profile, with all-family second-order scope explicit. -/
def Profile (B : Type) [PartialOrder B] : Prop :=
  Complementation B ∧ UnrestrictedSumOne B ∧ Unrestricted (B := B)

/-- The generic mathematical interpretation contains no assumption of atoms. -/
def PositiveProfile (A : Type) [CompleteBooleanAlgebra A] : Prop :=
  Profile (Positive A)

/-- Existing Mathlib regular elements of the frame of open real regions. -/
abbrev RegionAlgebra := Heyting.Regular (TopologicalSpace.Opens ℝ)

/-- Lift arbitrary suprema/infima through Mathlib's existing regularization
Galois insertion. Its lattice is the same one used by the Boolean instance. -/
noncomputable instance : CompleteBooleanAlgebra RegionAlgebra :=
  let L : CompleteLattice RegionAlgebra := Heyting.Regular.gi.liftCompleteLattice
  { (inferInstance : BooleanAlgebra RegionAlgebra) with
    sSup := L.sSup
    sInf := L.sInf
    isLUB_sSup := L.isLUB_sSup
    isGLB_sInf := L.isGLB_sInf }

/-- Empty region removed; ordinary subset inclusion remains the order. -/
abbrev Region := Positive RegionAlgebra

/-- Full profile and every object having a proper nonempty part are joint,
with explicit nonvacuity, absence of a least/null object and infinitude. -/
def GunkCertificate : Prop :=
  Nonempty Region ∧ Profile Region ∧
  (∀ U : Region, Composite U) ∧
  (¬ ∃ n : Region, ∀ U, n ≤ U) ∧ Infinite Region

/-- The old nonempty-subsets-of-Bool carrier is the atomistic contrast, under
exactly the same full profile, with no added null object. -/
def AtomicCertificate : Prop :=
  Nonempty Body ∧ Profile Body ∧
  TruthCore.Causality.AtomisticCausalSource.AtomicParts Body ∧
  (¬ ∃ n : Body, ∀ U, n ≤ U) ∧ Finite Body

/-- No finite inhabited partial order can make every object composite.
This does not imply that every infinite model is atomless. -/
def FiniteBoundary : Prop :=
  ∀ (B : Type) [PartialOrder B] [Nonempty B] [Finite B],
    ¬ (∀ x : B, Composite x)

end TruthCore.Mereology.AtomlessFusionProfile
