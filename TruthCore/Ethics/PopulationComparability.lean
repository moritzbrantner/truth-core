module

public import TruthCore.Ethics.PopulationScoring

/-! Analyst formulation, attribution deferred. The two coordinates name the
SAME two individuals across alternatives. Independently rescaling each person's
welfare preserves their own ordering but need not preserve interpersonal units.
This tests an explicit representation-invariance requirement, not welfare truth,
moral adequacy, or the actual availability of the compared profiles. -/

@[expose] public section
namespace TruthCore.Ethics.PopulationComparability
open PopulationScoring

abbrev Pair := ℝ × ℝ

def population (x : Pair) : Population := [x.1, x.2]

/-- Positive a,b preserve each individual's ordering; u,v are individual origins.
The same transformation is applied to both alternatives. -/
def reframe (a b u v : ℝ) (x : Pair) : Pair := (a * x.1 + u, b * x.2 + v)

/-- Simultaneous strict preference by three existing arithmetic policies.
Critical level c is shared across the two equal-sized alternatives. -/
def AllPrefer (c : ℝ) (x y : Pair) : Prop :=
  total (population x) < total (population y) ∧
  mean (population x) < mean (population y) ∧
  critical c (population x) < critical c (population y)

/-- Shared scale burden, guarded common-scale invariance and Pareto exception.
No representation-invariance requirement is declared morally authoritative. -/
def Controls : Prop :=
  (∀ x y c, AllPrefer c x y ↔ total (population x) < total (population y)) ∧
  (∀ a b u v x y, 0 < a → 0 < b →
    (((reframe a b u v x).1 < (reframe a b u v y).1 ↔ x.1 < y.1) ∧
     ((reframe a b u v x).2 < (reframe a b u v y).2 ↔ x.2 < y.2))) ∧
  (∀ x y u v, x.1 < y.1 → y.2 < x.2 →
    ∃ a b a' b', 0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧
      ∀ c, AllPrefer c (reframe a b u v x) (reframe a b u v y) ∧
        AllPrefer c (reframe a' b' u v y) (reframe a' b' u v x)) ∧
  (∀ x y a u v c, 0 < a →
    (AllPrefer c (reframe a a u v x) (reframe a a u v y) ↔ AllPrefer c x y)) ∧
  (∀ x y a b u v c, 0 < a → 0 < b → x.1 ≤ y.1 → x.2 ≤ y.2 →
    (x.1 < y.1 ∨ x.2 < y.2) →
    AllPrefer c (reframe a b u v x) (reframe a b u v y))

end TruthCore.Ethics.PopulationComparability
