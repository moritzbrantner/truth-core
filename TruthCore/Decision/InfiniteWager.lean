import Mathlib.Basic.ENNReal.Inv

/-!
Analyst's restricted nonnegative two-state wager profile, prompted by
Carneades.org, `Pascal's Wager`, p3ScupIbdkU, 03:33–05:50. This is not an
attributed formalization: public automatic captions were read, but no pinned
media witness has been materialized. It is not Pascal's historical argument.

`p` is the prior weight of the reward state and `q` the independent probability
of choosing the rewarded act. Its utility is top on success and zero otherwise.
The product is therefore the reward-state contribution to expected utility;
the remaining contributions are zero. No negative expenses, infinite losses,
salvation theology, belief voluntarism, or practical norm is encoded.
-/
namespace TruthCore.Decision.InfiniteWager

/-- Standard Mathlib extended nonnegative expectation for this zero-otherwise
profile. Genuine probabilities additionally satisfy `p ≤ 1` and `q ≤ 1`. -/
noncomputable def value (p q : ENNReal) : ENNReal := p * q * ⊤

/-- All nonzero mixture weights tie at top when the reward-state weight is
nonzero. Concrete distinct probabilities one and one-half therefore tie, with
zero-prior and zero-action controls. This is an ordinal comparison of extended
expectations, not a duty to act or evidence about which world obtains. -/
def MixtureTie : Prop :=
  (∀ p q : ENNReal, p ≠ 0 → q ≠ 0 → value p q = ⊤) ∧
  (∀ p : ENNReal, p ≠ 0 →
    value p 1 = value p (1 / 2) ∧ (1 : ENNReal) ≠ 1 / 2) ∧
  (∀ q : ENNReal, value 0 q = 0) ∧
  (∀ p : ENNReal, value p 0 = 0)

end TruthCore.Decision.InfiniteWager
