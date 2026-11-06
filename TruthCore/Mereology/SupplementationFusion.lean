module

public import TruthCore.Mereology.NecessaryPartFusionDecomposition
public import Mathlib.Data.Fintype.Basic

/-!
Analyst axiom comparison for #1050; attribution deferred. Navigation: SEP
Mereology §§3.1–3.2, 4.2–4.4, P.4/P.5 and (52_2)/(52_3).
One fixed Mathlib partial order and the existing common-part Overlap are used.
A null object is not silently excluded from arbitrary carriers: if present it
makes all objects overlap, so nontrivial supplementation cannot hold. The rival
explicitly has no null object. No genuine-overlap modification, world/existence
guard, grounding or actual ontology is built into this mathematical profile.
-/

@[expose] public section

namespace TruthCore.Mereology.SupplementationFusion
open UniversalFusionBoundary NecessaryPartFusionDecomposition

/-- Every proper part leaves a disjoint part of its whole. -/
def WeakSupplementation (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, x < y → ∃ z, z ≤ y ∧ ¬ Overlap z x

/-- Every failure of containment has a disjoint part witnessing the difference. -/
def StrongSupplementation (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, ¬ x ≤ y → ∃ z, z ≤ x ∧ ¬ Overlap z y

/-- Only two-member Sum2 formation, allowing repeated members. This is weaker
in quantifier scope than the existing all-nonempty-Set Unrestricted profile. -/
def BinaryFusion (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, ∃ u, Fusion {x, y} u

/-- Sum3 fixes overlap profile only; containment of members is not assumed. -/
def OverlapFusion {B : Type} [PartialOrder B] (family : Set B) (u : B) : Prop :=
  ∀ p, Overlap p u ↔ ∃ x ∈ family, Overlap p x

/-- All nonempty Lean Sets, exactly the second-order scope of Unrestricted;
empty-family formation and first-order-schema equivalence are not asserted. -/
def UnrestrictedOverlap (B : Type) [PartialOrder B] : Prop :=
  ∀ family : Set B, family.Nonempty → ∃ u, OverlapFusion family u

def SeparationCharacterization (B : Type) [PartialOrder B] : Prop :=
  StrongSupplementation B ↔ OverlapExtensionalParthood B

def FusionComparison (B : Type) [PartialOrder B] : Prop :=
  ∀ (family : Set B) (u : B), Fusion family u ↔ OverlapFusion family u

/-- Greatest candidate of this fixed carrier, with no ontological/modal role. -/
def GreatestEntity (B : Type) [PartialOrder B] : Prop :=
  ∃ u : B, ∀ x, x ≤ u

/-- Four candidates; two atoms and two incomparable duplicate composites.
This differs from the existing extensional nonempty-subset Body model. -/
inductive Rival where
  | a | b | u | v
  deriving DecidableEq

instance : Fintype Rival where
  elems := {.a, .b, .u, .v}
  complete := by intro x; cases x <;> simp

/-- Only a,b are strictly below u,v. -/
def rivalPart (x y : Rival) : Prop :=
  x = y ∨ ((x = .a ∨ x = .b) ∧ (y = .u ∨ y = .v))

instance : DecidableRel rivalPart := fun x y => by unfold rivalPart; infer_instance

instance : PartialOrder Rival where
  le := rivalPart
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Rival := inferInstanceAs (DecidableRel rivalPart)

/-- Joint rival certificate: formation is Sum3 for every nonempty family,
while selected Sum2 sums exist nonuniquely and global Sum2 formation fails.
No model of classical extensional mereology or actual material coincidence. -/
def RivalCertificate : Prop :=
  WeakSupplementation Rival ∧
  UnrestrictedOverlap Rival ∧
  ¬ StrongSupplementation Rival ∧
  ¬ OverlapExtensionalParthood Rival ∧
  Fusion ({Rival.a, Rival.b} : Set Rival) Rival.u ∧
  Fusion ({Rival.a, Rival.b} : Set Rival) Rival.v ∧
  Rival.u ≠ Rival.v ∧
  (∀ p : Rival, p < Rival.u ↔ p < Rival.v) ∧
  ¬ (∃ t : Rival, Rival.u ≤ t ∧ Rival.v ≤ t) ∧
  ¬ Unrestricted (B := Rival) ∧
  ¬ GreatestEntity Rival ∧
  ¬ (∃ n : Rival, ∀ x, n ≤ x) ∧
  OverlapFusion ({Rival.u, Rival.v} : Set Rival) Rival.u ∧
  ¬ Rival.v ≤ Rival.u

end TruthCore.Mereology.SupplementationFusion
