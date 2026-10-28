import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Abel

/-!
Analyst's one-dimensional configuration profile for the Leibniz–Clarke exchange.
Bodies are labeled, locations are real numbers, and a common static translation
changes no signed relative displacement or pair distance. Signed displacements
are stronger data than unsigned distances. No temporal trajectory, acceleration,
force, rotation or empirical completeness thesis is included.

The symmetry-breaking clause prohibits a deterministic selector of absolute
configurations from these relative data if the selector must also be equivariant
under every translation. That requirement is an explicit mathematical profile,
not an interpretation of every sufficient reason, divine act, or physical theory.
-/
namespace TruthCore.Space.TranslationBoundary

abbrev Configuration (B : Type) := B → ℝ

/-- Static common displacement in the chosen absolute real coordinate. -/
def shift {B : Type} (a : ℝ) (x : Configuration B) : Configuration B :=
  fun i => x i + a

/-- Signed relative displacements, not the whole physical state. -/
def relative {B : Type} (x : Configuration B) : B → B → ℝ :=
  fun i j => x i - x j

/-- Relational agreement in this explicitly oriented one-dimensional profile. -/
def Relative {B : Type} (x y : Configuration B) : Prop := relative x = relative y

/-- Origin anchoring chooses a representative; it is not an absolute location. -/
def normal {B : Type} (b : B) (x : Configuration B) : Configuration B :=
  fun i => x i - x b

/-- An extra covariance norm for a deterministic absolute-output selector. -/
def Covariant {B : Type} (select : (B → B → ℝ) → Configuration B) : Prop :=
  ∀ a x, select (relative (shift a x)) = shift a (select (relative x))

/-- Two inhabited distinct-position bodies, rather than a constant fixture. -/
def pair : Configuration Bool := fun i => if i then 1 else 0

/-- Geometry plus the precise symmetry-breaking obstruction. The supplied body
in the general clauses excludes an empty body type. No PSR, metaphysical identity,
physical-equivalence or preferred-ontology conclusion is encoded. -/
def Certificate : Prop :=
  (∀ (B : Type) (b : B) (x y : Configuration B),
    Relative x y ↔ ∃ a, y = shift a x) ∧
  (∀ (B : Type) (a : ℝ) (x : Configuration B) (i j : B),
    dist (shift a x i) (shift a x j) = dist (x i) (x j)) ∧
  (∀ (B : Type) (b : B) (a : ℝ) (x : Configuration B),
    shift a x = x ↔ a = 0) ∧
  (∀ (B : Type) (b : B), ¬ ∃ select : (B → B → ℝ) → Configuration B,
    Covariant select) ∧
  (∀ (B : Type) (b : B) (a : ℝ) (x : Configuration B),
    normal b (shift a x) = normal b x ∧ Relative x (normal b x)) ∧
  (pair false = 0 ∧ pair true = 1 ∧
    Relative pair (shift 1 pair) ∧ shift 1 pair ≠ pair ∧
    dist (pair false) (pair true) = 1) ∧
  (∃ select : (Empty → Empty → ℝ) → Configuration Empty, Covariant select)

end TruthCore.Space.TranslationBoundary
