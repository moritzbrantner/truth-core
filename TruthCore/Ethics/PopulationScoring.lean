module

public import TruthCore.Ethics.PopulationAggregation
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Analyst formulations, attribution deferred. A finite list explicitly assigns
one real welfare to each individual; list order has no scoring significance.
The common cardinal interpersonal scale and admissible arbitrary finite
replication are framework inputs, not ethical or practical conclusions. -/

@[expose] public section

namespace TruthCore.Ethics.PopulationScoring

abbrev Population := List ℝ

/-- Anonymous separable additive score; the empty population has score zero. -/
def score (f : ℝ → ℝ) (p : Population) : ℝ := (p.map f).sum

def total (p : Population) : ℝ := score id p

/-- Only nonempty populations are compared by average below. The arithmetic
extension to the empty list is zero and carries no ethical interpretation. -/
noncomputable def mean (p : Population) : ℝ := total p / (p.length : ℝ)

noncomputable def summary (p : Population) (h : 0 < p.length) : PopulationAggregation.Profile :=
  ⟨p.length, h, mean p⟩

/-- Explicit representation assumption for a proposed population value. -/
def Additive (f : ℝ → ℝ) (value : Population → ℝ) : Prop :=
  ∀ p, value p = score f p

def PositiveLifeScore (f : ℝ → ℝ) : Prop := ∀ w, 0 < w → 0 < f w

/-- Fixed baseline and positive low-welfare cutoff: no nonempty uniform
replication below this cutoff strictly outranks the baseline. This is narrower
than any unrestricted population-ethics impossibility claim. -/
def NoLowReplication (value : Population → ℝ) (p : Population) (δ : ℝ) : Prop :=
  ∀ w, 0 < w → w < δ → ∀ n : Nat, 0 < n → value (List.replicate n w) ≤ value p

/-- Positive critical levels penalize each additional life below c. -/
def critical (c : ℝ) (p : Population) : ℝ := score (fun w => w - c) p

/-- Generic obstruction, incompatible bundle, omission witnesses, distribution
and policy costs. All guards are internal to this conditional certificate;
there are no independently established moral premises or root discharges. -/
def Controls : Prop :=
  (∀ p h, (summary p h).total = total p) ∧
  (∀ f value, Additive f value → ∀ p w, 0 < f w →
    ∃ n : Nat, 0 < n ∧ value p < value (List.replicate n w)) ∧
  (∀ f value, Additive f value → PositiveLifeScore f → ∀ p δ, 0 < δ →
    ∃ w, 0 < w ∧ w < δ ∧ ∃ n : Nat, 0 < n ∧
      value p < value (List.replicate n w)) ∧
  (∀ f value p δ, 0 < δ → Additive f value → PositiveLifeScore f →
    ¬ NoLowReplication value p δ) ∧
  (∀ p δ, NoLowReplication (score (fun _ => 0)) p δ) ∧
  (∀ p, 0 < p.length → 0 < mean p → NoLowReplication mean p (mean p)) ∧
  (¬ ∃ f, Additive f mean) ∧
  (∀ c, 0 < c → NoLowReplication (critical c) [c + 1] c ∧
    ¬ PositiveLifeScore (fun w => w - c)) ∧
  (∀ p c w, 0 < w → w < c → critical c (p ++ [w]) < critical c p) ∧
  (∀ p w, 0 < p.length → 0 < w → w < mean p →
    mean (p ++ [w]) < mean p ∧ total p < total (p ++ [w])) ∧
  (∀ n w, 0 < n → mean (List.replicate n w) = w) ∧
  (total [1, 1] = total [-1, 3] ∧ mean [1, 1] = mean [-1, 3] ∧
    (∀ w ∈ ([1, 1] : Population), 0 < w) ∧
    (∃ w ∈ ([-1, 3] : Population), w < 0)) ∧
  (∀ p N w, 0 < N → 0 < w → (N : ℝ) * w ≤ total p →
    ∀ n : Nat, n ≤ N → total (List.replicate n w) ≤ total p)

end TruthCore.Ethics.PopulationScoring
