module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import TruthCore.Results.Decision.InfiniteWager.Solution

/-! Working reconstruction from `docs/notes/carneades-decision-wager.md`.
Attribution is deferred. Utilities use Mathlib's extended *signed* reals.
An act is a feasible behavioral lottery, not a voluntarily selected belief.
No decision norm, theological utility, or empirical prior is established. -/

@[expose] public section

namespace TruthCore.Decision.SignedWager

/-- Real probability; complementary state/action weight is `1 - p`. -/
def Probability (p : ℝ) : Prop := 0 ≤ p ∧ p ≤ 1

/-- Partial addition refuses opposing infinities before Mathlib's totalized
addition can assign them any value. Zero-weight impossible outcomes are zero. -/
noncomputable def add (x y : EReal) : Option EReal :=
  if (x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤) then none else some (x + y)

/-- Two complementary-state expectation, partial only at opposing infinities.
The probability guard is a separate explicit assumption, not a silent coercion. -/
noncomputable def expectation (p : ℝ) (u v : EReal) : Option EReal :=
  add ((p : EReal) * u) (((1 - p : ℝ) : EReal) * v)

/-- Single rewarded policy: success probability `p*q`; finite utility `c` in
all remaining cases. `c` can be negative. This collapses equal finite outcomes,
not opposing infinite outcomes. Independence of state and mixed act is stipulated. -/
noncomputable def single (p q c : ℝ) : Option EReal :=
  expectation (p * q) ⊤ c

/-- Two incompatible reward policies with complementary prior weights. Policy
one rewards act one, policy two rewards act two; both give the same signed
finite utility on failure. `q` is an independent act-one lottery. -/
noncomputable def many (p q c : ℝ) : Option EReal :=
  expectation (p * q + (1 - p) * (1 - q)) ⊤ c

/-- A maximizer compares defined expectations only; undefined is not a score. -/
def Maximizes (f : ℝ → Option EReal) (q : ℝ) : Prop :=
  Probability q ∧ ∃ v, f q = some v ∧
    ∀ r w, Probability r → f r = some w → w ≤ v

/-- Full signed-cost, many-policy and omission controls. Universals are scoped
conditional mathematics, not unproved source commitments. -/
def SignedConsequences : Prop :=
  TruthCore.Decision.InfiniteWager.MixtureTie ∧
  (∀ p q c : ℝ, Probability p → Probability q → 0 < p → 0 < q →
    single p q c = some ⊤) ∧
  (∀ p q : ℝ, Probability p → Probability q →
    Probability (p * q + (1 - p) * (1 - q))) ∧
  (∀ p q c : ℝ, 0 < p → p < 1 → Probability q →
    many p q c = some ⊤) ∧
  (∀ c : ℝ, single 0 1 c = some (c : EReal) ∧
    single 1 0 c = some (c : EReal)) ∧
  (∀ p : ℝ, 0 < p → p < 1 → expectation p ⊤ ⊥ = none) ∧
  (∀ c : ℝ, expectation 0 ⊤ c = some (c : EReal)) ∧
  (∀ c : ℝ, expectation 1 ⊤ c = some ⊤)

/-- A real finite-cost model where the religious reward state is false at the
actual world (false), yet an act is an expectation maximizer under the agent's
non-dogmatic prior. No act-to-belief-control relation is encoded. -/
def PracticalNontruth : Prop :=
  ∃ (religious : Bool → Prop) (actual : Bool) (p q c : ℝ),
    ¬ religious actual ∧ religious true ∧ Probability p ∧ 0 < p ∧ p < 1 ∧
    c < 0 ∧ Maximizes (single p · c) q ∧
    (∀ r, Probability r → Maximizes (many p · c) r) ∧
    single p 1 c = single p (1 / 2) c ∧ (1 : ℝ) ≠ 1 / 2 ∧
    single 0 1 c ≠ some ⊤ ∧ single 1 0 c ≠ some ⊤

end TruthCore.Decision.SignedWager
