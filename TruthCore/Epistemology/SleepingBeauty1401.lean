module

public import Mathlib.Algebra.Order.Field.Rat
public import TruthCore.Logic.CorrectionCriterion
import Mathlib.Tactic.NormNum

/-! Analyst formulation for #1401, attribution deferred. A coin world is a
whole experiment; a center additionally specifies an awakening. Rational masses
are finite exact weights, not a claimed uniquely rational self-locating prior.
The applicability of either sampling rule to Beauty's credence is OPEN. -/

@[expose] public section
namespace TruthCore.Epistemology.SleepingBeauty1401

inductive World where | heads | tails deriving DecidableEq
inductive Center where | headsMonday | tailsMonday | tailsTuesday deriving DecidableEq

def world : Center → World
  | .headsMonday => .heads
  | .tailsMonday | .tailsTuesday => .tails

def monday : Center → Bool
  | .headsMonday | .tailsMonday => true
  | .tailsTuesday => false

/-- All three masses are nonnegative and jointly normalized. Zero Tuesday is
allowed, so positivity cannot silently enter an incompatibility proof. -/
structure Allocation where
  h : ℚ
  m : ℚ
  t : ℚ
  h_nonneg : 0 ≤ h
  m_nonneg : 0 ≤ m
  t_nonneg : 0 ≤ t
  normalized : h + m + t = 1

def mass (a : Allocation) : Center → ℚ
  | .headsMonday => a.h
  | .tailsMonday => a.m
  | .tailsTuesday => a.t

/-- Conditional event probability; its nonzero denominator is in M. -/
def headsGivenMonday (a : Allocation) : ℚ := a.h / (a.h + a.m)
def N (a : Allocation) : Prop := a.h = 1/2
def M (a : Allocation) : Prop := 0 < a.h + a.m ∧ headsGivenMonday a = 1/2
def S (a : Allocation) : Prop := a.m = a.t
def P (a : Allocation) : Prop := 0 < a.t

def thirds : Allocation := ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num⟩
def halves : Allocation := ⟨1/2, 1/4, 1/4, by norm_num, by norm_num, by norm_num, by norm_num⟩
def zeroTuesday : Allocation := ⟨1/2, 1/2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

def Incompatibility : Prop :=
  (∀ a, N a → M a → a.t = 0) ∧
  (∀ a, ¬ (N a ∧ M a ∧ P a)) ∧
  (∀ a, ¬ (N a ∧ M a ∧ S a)) ∧
  (∀ a, N a → P a → 1/2 < headsGivenMonday a)

/-- Omission witnesses establish minimality relative to Allocation's background,
not a defeat of either rational-update account. Both live models have full support. -/
def OmissionControls : Prop :=
  (M thirds ∧ S thirds ∧ P thirds ∧ ¬ N thirds) ∧
  (N halves ∧ S halves ∧ P halves ∧ ¬ M halves ∧ headsGivenMonday halves = 2/3) ∧
  (N zeroTuesday ∧ M zeroTuesday ∧ ¬ S zeroTuesday ∧ ¬ P zeroTuesday) ∧
  (0 < thirds.h ∧ 0 < thirds.m ∧ 0 < thirds.t) ∧
  (0 < halves.h ∧ 0 < halves.m ∧ 0 < halves.t)

/-- p is an experiment prior; k is a positive count of Tails awakenings.
Each world is retained once by experiment sampling, whereas awakening sampling
weights its prior by its awakening count (one for Heads, k for Tails).
No actual sampling mechanism is attributed to Beauty's situation. -/
structure Protocol where
  p : ℚ
  k : ℕ
  p_pos : 0 < p
  p_lt_one : p < 1
  k_pos : 0 < k

def awakeningNormalizer (q : Protocol) : ℚ := q.p + q.k * (1-q.p)
/-- A selector first chooses a coin experiment with prior p, independently
chooses one of k potential awakening slots uniformly, and retains the selection
only if an awakening exists in that slot. All k Tails slots exist, but only
one Heads slot does. This is a stipulated external selector, not Beauty. -/
def slotHeads (q : Protocol) : ℚ := (q.p / q.k) / (q.p / q.k + (1-q.p))
def experimentHeads (q : Protocol) : ℚ := q.p
def awakeningHeads (q : Protocol) : ℚ := q.p / awakeningNormalizer q

/-- Unit Heads ticket at price c. Once-per-experiment settlement charges and
pays once; per-awakening settlement charges on each awakening, pays on the one
Heads awakening. Linear additive utility and the same fixed policy are stipulated.
These are prospective expectations under the experiment prior, not conditional
expected utilities for an individual awakening or a Dutch-book theorem. -/
def experimentGain (q : Protocol) (c : ℚ) : ℚ := q.p * (1-c) + (1-q.p) * (-c)
def awakeningGain (q : Protocol) (c : ℚ) : ℚ :=
  q.p * (1-c) + (1-q.p) * q.k * (-c)

def WeightingAndWagers : Prop := ∀ q : Protocol,
  slotHeads q = awakeningHeads q ∧
  0 < awakeningNormalizer q ∧
  0 < awakeningHeads q ∧ awakeningHeads q < 1 ∧
  (awakeningHeads q = experimentHeads q ↔ q.k = 1) ∧
  (1 < q.k → awakeningHeads q < experimentHeads q) ∧
  (∀ c, experimentGain q c = q.p-c) ∧
  (∀ c, awakeningGain q c = q.p-c*awakeningNormalizer q) ∧
  (∀ c, experimentGain q c = 0 ↔ c = experimentHeads q) ∧
  (∀ c, awakeningGain q c = 0 ↔ c = awakeningHeads q)

/-- Awakening appearance alone is constant across all centers. Compose the
existing extensional criterion theorem to show it cannot perfectly classify
Heads. This does not show that uninformative appearances require no credence
update: exact truth classification and probabilistic weighting are distinct. -/
def AppearanceBoundary : Prop :=
  ¬ TruthCore.Logic.CorrectionCriterion.AdmitsCriterion
    (fun _ : Center => ()) (fun c => world c = .heads)

end TruthCore.Epistemology.SleepingBeauty1401
