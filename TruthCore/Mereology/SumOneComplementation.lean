module

public import TruthCore.Mereology.SupplementationFusion
public import Mathlib.Order.Bounds.Basic

/-! Analyst formulations for #1054; attribution deferred. Navigation: SEP
Mereology §§3.3, 4.3–4.4, P.6 and (52_1). Sum1 is Mathlib's least upper
bound, not merely a minimal upper bound. The same fixed partial order and
common-part Overlap used by Sum2/Sum3 remain in force. Formation quantifies
over all nonempty Lean Sets, an explicit second-order profile, not a claim of
first-order schema equivalence. No modal, causal or actual-ontology bridge.
-/

@[expose] public section

namespace TruthCore.Mereology.SumOneComplementation
open UniversalFusionBoundary SupplementationFusion

/-- Exact remainder y minus x whenever y is not contained in x. Its parts
are all and only the parts of y disjoint from x, stronger than one SS witness.
No null object or empty remainder is demanded when y ≤ x. -/
def Complementation (B : Type) [PartialOrder B] : Prop :=
  ∀ x y : B, ¬ y ≤ x → ∃ z : B, ∀ w : B,
    w ≤ z ↔ w ≤ y ∧ ¬ Overlap w x

/-- Sum1 formation: each nonempty family has its order-theoretic least upper
bound. This by itself does not assert the Sum2 no-extra-parts condition. -/
def UnrestrictedSumOne (B : Type) [PartialOrder B] : Prop :=
  ∀ family : Set B, family.Nonempty → ∃ u, IsLUB family u

/-- Pointwise coincidence on nonempty families, with formation separate. -/
def SumOneComparison (B : Type) [PartialOrder B] : Prop :=
  ∀ (family : Set B), family.Nonempty → ∀ u : B,
    IsLUB family u ↔ Fusion family u

/-- Three incomparable atoms under one top. This is not the earlier two-atoms,
two-duplicate-wholes rival: here all joins and strong supplementation exist. -/
inductive JoinRival where
  | a | b | c | top
  deriving DecidableEq

instance : Fintype JoinRival where
  elems := {.a, .b, .c, .top}
  complete := by intro x; cases x <;> simp

def rivalPart (x y : JoinRival) : Prop := x = y ∨ y = .top
instance : DecidableRel rivalPart := fun _ _ => by unfold rivalPart; infer_instance
instance : PartialOrder JoinRival where
  le := rivalPart
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
instance : DecidableLE JoinRival := inferInstanceAs (DecidableRel rivalPart)

/-- Two incomparable atoms, with equality parthood. A separate type prevents
confusing this order with Bool's ordinary order. -/
inductive AtomPair where
  | a | b
  deriving DecidableEq
instance : Fintype AtomPair where
  elems := {.a, .b}
  complete := by intro x; cases x <;> simp
def atomPart (x y : AtomPair) : Prop := x = y
instance : DecidableRel atomPart := fun _ _ => by unfold atomPart; infer_instance
instance : PartialOrder AtomPair where
  le := atomPart
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
instance : DecidableLE AtomPair := inferInstanceAs (DecidableRel atomPart)

/-- Joint mathematical controls. The first has SS and every nonempty Sum1,
but no Sum2 of {a,b}; the second has exact remainders but lacks that formation.
Both have no null object. No physical or metaphysical possibility is asserted. -/
def RivalCertificate : Prop :=
  StrongSupplementation JoinRival ∧
  UnrestrictedSumOne JoinRival ∧
  IsLUB ({JoinRival.a, JoinRival.b} : Set JoinRival) JoinRival.top ∧
  ¬ (∃ u : JoinRival, Fusion {JoinRival.a, JoinRival.b} u) ∧
  ¬ Complementation JoinRival ∧
  ¬ (∃ n : JoinRival, ∀ x, n ≤ x) ∧
  Complementation AtomPair ∧
  ¬ (∃ u : AtomPair, IsLUB {AtomPair.a, AtomPair.b} u) ∧
  ¬ (∃ u : AtomPair, Fusion {AtomPair.a, AtomPair.b} u) ∧
  ¬ (∃ n : AtomPair, ∀ x, n ≤ x)

end TruthCore.Mereology.SumOneComplementation
