/-! Explicit analyst profiles for the Sorites problem, not an attribution to a
historical author. The chain index measures successive cases, not temporal or
causal order. A binary predicate gives a determinate extension; its decidability
in the boundary theorem is an explicit assumption, not a theory of all vague
language. Weak non-opposition for a partial classification is a different rule. -/
namespace TruthCore.Logic.SoritesBoundary

/-- Truth preservation across every adjacent step up to the endpoint. It does
not assert that neighboring cases are perceptually distinguishable. -/
def Tolerance (P : Nat → Prop) (n : Nat) : Prop :=
  ∀ k, k < n → P k → P (k + 1)

/-- A positive case immediately followed by a case outside the predicate. No
claim about our knowledge or perceptual access to this boundary is implicit. -/
def Boundary (P : Nat → Prop) (n : Nat) : Prop :=
  ∃ k, k < n ∧ P k ∧ ¬ P (k + 1)

/-- A stipulated partial classification, not a fuzzy truth degree or a complete
supervaluation semantics. Borderline is neither positive nor negative. -/
inductive Status where
  | positive | borderline | negative
  deriving DecidableEq

/-- Adjacent statuses are not opposed determinate classifications. Unlike
Tolerance, positive-to-borderline and borderline-to-negative are permitted. -/
def NonOpposed (a b : Status) : Prop :=
  ¬ (a = .positive ∧ b = .negative) ∧
  ¬ (a = .negative ∧ b = .positive)

def partialProfile : Nat → Status
  | 0 => .positive
  | 1 => .borderline
  | _ + 2 => .negative

/-- Conditional binary boundary theorem, incompatible triple, deletion
controls, and a distinct three-status non-opposition control. The binary core
has three independently necessary members, witnessed already at length one;
the partial control has length two. No metaphysical or linguistic adequacy
claim, mandatory community, real heap threshold, or root closure follows. -/
def Certificate : Prop :=
  (∀ n (P : Nat → Prop) [DecidablePred P], P 0 → ¬ P n → Boundary P n) ∧
  (∀ n (P : Nat → Prop), ¬ (P 0 ∧ ¬ P n ∧ Tolerance P n)) ∧
  ((∃ P : Nat → Prop, ¬ P 0 ∧ ¬ P 1 ∧ Tolerance P 1) ∧
   (∃ P : Nat → Prop, P 0 ∧ P 1 ∧ Tolerance P 1) ∧
   (∃ P : Nat → Prop, P 0 ∧ ¬ P 1 ∧ ¬ Tolerance P 1)) ∧
  (partialProfile 0 = .positive ∧ partialProfile 2 = .negative ∧
   (∀ k, k < 2 → NonOpposed (partialProfile k) (partialProfile (k+1))) ∧
   ¬ Tolerance (fun k => partialProfile k = .positive) 2)

end TruthCore.Logic.SoritesBoundary
