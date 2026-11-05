module

public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import TruthCore.Logic.CorrectionCriterion
public import TruthCore.Logic.EpistemicAccuracy
public import TruthCore.Logic.TranscendentalPractice

/-! Analyst formulation for #931, attribution deferred. A finite pool supplies
binary predictions before each feedback label. Rational weights start at one;
weighted majority breaks ties in favor of true; disagreeing experts lose half
of their weight. Actual truth is a separate stream, never an algorithm input.
This is a repeated binary prediction protocol, not an exact truth classifier,
probability estimate or theory of justification. All arithmetic is Mathlib's.
-/

@[expose] public section
namespace TruthCore.Logic.FallibleCorrection

/-- Number of disagreements on the first n rounds (round n is excluded). -/
def mistakes (a b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => mistakes a b n + if a n = b n then 0 else 1

/-- Total positive vote mass for the supplied binary prediction. -/
def mass {N : ℕ} (w : Fin N → ℚ) (advice : Fin N → Bool) (b : Bool) : ℚ :=
  ∑ i, if advice i = b then w i else 0

/-- Finite, exact and computable weighted vote, including its tie rule. -/
def predict {N : ℕ} (w : Fin N → ℚ) (advice : Fin N → Bool) : Bool :=
  decide (mass w advice false ≤ mass w advice true)

/-- An observed disagreement discounts the expert; feedback need not be true. -/
def update {N : ℕ} (w : Fin N → ℚ) (advice : Fin N → Bool) (feedback : Bool)
    (i : Fin N) : ℚ := if advice i = feedback then w i else w i / 2

/-- State before round n, using exactly feedback from rounds less than n. -/
def weights {N : ℕ} (advice : ℕ → Fin N → Bool) (feedback : ℕ → Bool) :
    ℕ → Fin N → ℚ
  | 0 => fun _ => 1
  | n+1 => update (weights advice feedback n) (advice n) (feedback n)

/-- The learner sees current advice and past feedback, never current truth. -/
def learner {N : ℕ} (advice : ℕ → Fin N → Bool) (feedback : ℕ → Bool)
    (n : ℕ) : Bool := predict (weights advice feedback n) (advice n)

/-- Exact potential guarantee, for arbitrary advice and feedback streams.
The second bound composes the guarantee with a corruption count: if observed
learner mistakes are at most b, actual mistakes are at most b+k. Expert
observed mistakes are at most its actual mistakes+k. No perfect expert,
stationarity, probability, normative authority or corruption oracle is assumed.
The witness i makes the pool nonempty. -/
def Performance : Prop := ∀ (N : ℕ) (advice : ℕ → Fin N → Bool)
    (feedback truth : ℕ → Bool) (n : ℕ) (i : Fin N),
  (1/2 : ℚ) ^ mistakes (fun t => advice t i) feedback n ≤
    (N : ℚ) * (3/4 : ℚ) ^ mistakes (learner advice feedback) feedback n ∧
  mistakes (learner advice feedback) truth n ≤
    mistakes (learner advice feedback) feedback n + mistakes feedback truth n ∧
  mistakes (fun t => advice t i) feedback n ≤
    mistakes (fun t => advice t i) truth n + mistakes feedback truth n

/-- Explicit truth-relative bound with at most k false feedback labels. The
subtraction is truncated at zero. If one expert has few actual errors and k is
small, large actual learner error is ruled out. Availability of a justified k
or of a good expert is not certified by the feedback itself. -/
def RobustPerformance : Prop := ∀ (N : ℕ) (advice : ℕ → Fin N → Bool)
    (feedback truth : ℕ → Bool) (n k : ℕ) (i : Fin N),
  mistakes feedback truth n ≤ k →
  (1/2 : ℚ) ^ (mistakes (fun t => advice t i) truth n + k) ≤
    (N : ℚ) * (3/4 : ℚ) ^ (mistakes (learner advice feedback) truth n - k)

/-- A numerical consequence allowing an imperfect expert AND false feedback:
for any horizon, two experts including one with at most two actual mistakes,
and at most one corrupted label, imply at most ten actual learner mistakes.
The good expert need not be identifiable or preselected by the algorithm. -/
def TwoExpertBudget : Prop := ∀ (advice : ℕ → Fin 2 → Bool)
    (feedback truth : ℕ → Bool) (n : ℕ) (i : Fin 2),
  mistakes (fun t => advice t i) truth n ≤ 2 →
  mistakes feedback truth n ≤ 1 →
  mistakes (learner advice feedback) truth n ≤ 10

/-- Concrete two-expert trace: both experts are constant, one false and one
true. One false feedback label moves the initial tie prediction true to false;
then truthful feedback restores true. In a false actual world this first update
corrects an error; in a true actual world the same reports mislead. -/
def traceAdvice (_ : ℕ) (i : Fin 2) : Bool := decide (i.val = 1)
def traceFeedback (t : ℕ) : Bool := decide (t ≠ 0)

def TraceControls : Prop :=
  learner traceAdvice traceFeedback 0 = true ∧
  learner traceAdvice traceFeedback 1 = false ∧
  learner traceAdvice traceFeedback 2 = true ∧
  weights traceAdvice traceFeedback 1 0 = 1 ∧
  weights traceAdvice traceFeedback 1 1 = 1/2 ∧
  mistakes (learner traceAdvice traceFeedback) (fun _ => true) 3 = 1 ∧
  mistakes traceFeedback (fun _ => true) 3 = 1 ∧
  mistakes (fun t => traceAdvice t 1) (fun _ => true) 3 = 0 ∧
  ¬ CorrectionCriterion.AdmitsCriterion
    (fun _ : Bool => (traceAdvice, traceFeedback)) (fun actual => actual = true)

/-- Two experts, one always true and one always false, with wholly false
feedback when truth is always true: the learner makes an actual error on every
round after the initial tie. Agreement with its supplied feedback is not truth.
-/
def Misleading : Prop :=
  ∀ n, learner traceAdvice (fun _ => false) (n+1) = false

/-- When feedback labels are false and actual truth is false, the initial
mistake is corrected forever after. A fixed true predictor makes n+1 mistakes.
Both streams can have the same reports in a true world, where this same update
fails: recovery here is a conditional example, not self-certified reliability. -/
def Recovery : Prop := ∀ n,
  mistakes (learner traceAdvice (fun _ => false)) (fun _ => false) (n+1) = 1 ∧
  mistakes (fun _ => true) (fun _ => false) (n+1) = n+1

/-- Integrated protocol properties and imported epistemic boundaries. The
accuracy theorems remain their original comparisons, not warrant for feedback. -/
def Certificate : Prop := Performance ∧ RobustPerformance ∧ TwoExpertBudget ∧ TraceControls ∧ Misleading ∧ Recovery ∧
  CorrectionCriterion.CriterionCharacterizationAndControls ∧
  EpistemicAccuracy.Certificate ∧ EpistemicAccuracy.DominanceCertificate ∧
  TranscendentalPractice.InquiryAccessBoundary

end TruthCore.Logic.FallibleCorrection
