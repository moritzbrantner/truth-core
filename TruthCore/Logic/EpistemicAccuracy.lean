module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Analyst accuracy comparison for #930; attribution deferred. Binary credences
are real numbers; substantive use restricts them to [0,1]. `q` is an independently
warranted probability assessment, not a definition of truth or a factive oracle.
The algebra alone supplies no normative predicate or authority. -/

@[expose] public section
namespace TruthCore.Logic.EpistemicAccuracy

/-- Expected binary squared error: q weights truth (outcome 1), 1-q falsity
(outcome 0). This is one explicitly selected accuracy measure, not a utility
function combining comfort, morality and truth. -/
def error (q r : ℝ) : ℝ := q * (1-r)^2 + (1-q) * r^2

/-- Rational uncertainty about q is allowed: every admitted q lies within ε
of the independently supplied estimate c. This does not assert calibration. -/
def Within (q c ε : ℝ) : Prop := -ε ≤ q-c ∧ q-c ≤ ε

/-- Cost of departing from q, strict uniqueness, and a robust guarantee when
the departure exceeds twice the admitted error in one's probability estimate.
The final concrete case separates epistemic error from combined practical cost:
a comfort reward can outweigh error without eliminating that error. -/
def Certificate : Prop :=
  (∀ q r : ℝ, error q r - error q q = (r-q)^2) ∧
  (∀ q r : ℝ, error q q ≤ error q r) ∧
  (∀ q r : ℝ, error q r = error q q ↔ r=q) ∧
  (∀ q c r ε : ℝ, 0 ≤ ε → Within q c ε →
    (c + 2*ε < r ∨ r < c - 2*ε) → error q c < error q r) ∧
  (error (1/2) 1 - error (1/2) (1/2) = 1/4 ∧
    error (1/2) 1 - 1 < error (1/2) (1/2))

/-- Simultaneous confidence in p and not-p, scored in each possible truth state.
No probability or evidence estimate enters this statewise comparison. -/
def pairError (truth : Bool) (r s : ℝ) : ℝ :=
  if truth then (1-r)^2 + s^2 else r^2 + (1-s)^2

noncomputable def projectFirst (r s : ℝ) : ℝ := (1+r-s)/2
noncomputable def projectSecond (r s : ℝ) : ℝ := (1-r+s)/2

/-- Project two [0,1] complementary credences to coherence. An incoherent
pair strictly loses in BOTH truth states by the same exact amount. This does
not dominate every coherent but wishful assessment. -/
def DominanceCertificate : Prop := ∀ r s : ℝ,
  0 ≤ r → r ≤ 1 → 0 ≤ s → s ≤ 1 →
  0 ≤ projectFirst r s ∧ projectFirst r s ≤ 1 ∧
  0 ≤ projectSecond r s ∧ projectSecond r s ≤ 1 ∧
  projectFirst r s + projectSecond r s = 1 ∧
  (∀ truth, pairError truth r s -
    pairError truth (projectFirst r s) (projectSecond r s) = (r+s-1)^2/2) ∧
  (r+s ≠ 1 → ∀ truth, pairError truth (projectFirst r s) (projectSecond r s) <
    pairError truth r s)

end TruthCore.Logic.EpistemicAccuracy
