import Mathlib.Data.Set.Lattice.Bounded

/-!
An analyst's scope test for #328. Varzi, SEP Mereology §4.4, definition (59),
introduces the universal entity; §4.5 distinguishes fusion from composition as
identity. The mathematical clauses below are not attributed causal principles.
A carrier denotes one fixed domain, with no implicit world or existence guard.
Mathlib's subset partial order supplies parthood in the nonempty-set model.
-/
namespace TruthCore.Mereology.UniversalFusionBoundary

/-- Common-part overlap; empty sets are excluded from the concrete carrier. -/
def Overlap {B : Type} [PartialOrder B] (x y : B) : Prop :=
  ∃ p, p ≤ x ∧ p ≤ y

/-- Sum2 profile: upper bound plus every part overlapping a selected member.
Unlike an arbitrary least upper bound this includes the no-extra-parts clause.
Quantifying over all Lean predicates is this analyst's explicit second-order
profile, not a claim that first-order axiom schemas quantify over every subset. -/
def Fusion {B : Type} [PartialOrder B] (family : Set B) (u : B) : Prop :=
  (∀ x ∈ family, x ≤ u) ∧
  ∀ p, p ≤ u → ∃ x ∈ family, Overlap p x

def Unrestricted {B : Type} [PartialOrder B] : Prop :=
  ∀ family : Set B, family.Nonempty → ∃ u, Fusion family u

/-- The selected whole covers the specified material domain, not necessarily
all entities in a larger metaphysical carrier. -/
def Covers {B : Type} [PartialOrder B] (material : B → Prop) (u : B) : Prop :=
  ∀ x, material x → x ≤ u

/-- At least one proper part, with no inference about causal dependence. -/
def Composite {B : Type} [PartialOrder B] (x : B) : Prop := ∃ p, p < x

/-- Distinct cause, matching only the numerical distinction in q3's
uniting-cause requirement. It need not be a nonpart of its effect. -/
def DistinctCause {B : Type} (cause : B → B → Prop) (x : B) : Prop :=
  ∃ c, c ≠ x ∧ cause c x

/-- Outside-parts cause, a strictly different optional relation condition. -/
def OutsideCause {B : Type} [PartialOrder B] (cause : B → B → Prop) (x : B) : Prop :=
  ∃ c, ¬ c ≤ x ∧ cause c x

/-- Material entities are nonempty subsets of two constituents. The model is
finite and atomistic; no claim about all universalist ontologies is made. -/
abbrev Body := {s : Set Bool // s.Nonempty}

def atom (b : Bool) : Body := ⟨{b}, ⟨b, rfl⟩⟩
def whole : Body := ⟨Set.univ, ⟨false, trivial⟩⟩

/-- Same parthood/fusion facts admit either of these independently interpreted
candidate ground relations. Strict parthood is a model interpretation, not a
definition of actual grounding. Neither interpretation adds a new object. -/
def partGround (x y : Body) : Prop := x < y
def noGround (_ _ : Body) : Prop := False

/-- Extend the domain by one nonmaterial candidate. Its not being part of the
material whole is explicit; no metaphysical possibility is inferred. -/
inductive Extended where
  | material (x : Body)
  | nonmaterial

def extendedPart : Extended → Extended → Prop
  | .material x, .material y => x ≤ y
  | .nonmaterial, .nonmaterial => True
  | _, _ => False

def externalControl : Prop :=
  extendedPart (.nonmaterial) (.nonmaterial) ∧
  ¬ extendedPart (.nonmaterial) (.material whole)

/-- One certificate packages a general scope constraint and concrete controls.
No organization, soul, historical attribution, actual causation, or root
premise is inferred from these formal models. -/
def Boundary : Prop :=
  (∀ (B : Type) [PartialOrder B] [Nonempty B],
    Unrestricted (B := B) → ∃ u : B, ∀ x, x ≤ u) ∧
  (∀ (B : Type) [PartialOrder B] (material : B → Prop) (u : B),
    Covers material u → ∀ c, ¬ c ≤ u → ¬ material c) ∧
  Unrestricted (B := Body) ∧
  Composite whole ∧
  DistinctCause partGround whole ∧
  (∀ x : Body, Composite x → DistinctCause partGround x) ∧
  (∀ x : Body, ¬ partGround x x) ∧
  ¬ (∀ x : Body, Composite x → DistinctCause noGround x) ∧
  (∀ cause : Body → Body → Prop, ¬ OutsideCause cause whole) ∧
  externalControl

end TruthCore.Mereology.UniversalFusionBoundary
