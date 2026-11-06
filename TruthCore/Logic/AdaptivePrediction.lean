module

public import TruthCore.Logic.FallibleCorrection

/-! Analyst formulation for #1058/#931; attribution deferred. Histories contain
only already observed truthful labels, newest first. A predictor is total and
deterministic; no computational bound or probabilistic interpretation is added.
The diagonal environment depends on the predictor. This does not assert a
single stream defeats every predictor, or identify meaning with prediction.
-/

@[expose] public section
namespace TruthCore.Logic.AdaptivePrediction
open FallibleCorrection

abbrev Predictor := List Bool → Bool

/-- The actual finite past of one supplied stream, excluding the current label. -/
def past (truth : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => truth n :: past truth n

def forecast (p : Predictor) (truth : ℕ → Bool) (n : ℕ) : Bool :=
  p (past truth n)

/-- Build one compatible chain of histories, not a fresh choice per horizon. -/
def history (p : Predictor) : ℕ → List Bool
  | 0 => []
  | n+1 => (!(p (history p n))) :: history p n

def diagonal (p : Predictor) (n : ℕ) : Bool := !(p (history p n))

/-- Coherence, failure at each step, and exact reused finite mistake counts. -/
def DiagonalBoundary : Prop := ∀ p : Predictor,
  (∀ n, history p n = past (diagonal p) n) ∧
  (∀ n, forecast p (diagonal p) n ≠ diagonal p n) ∧
  (∀ n, mistakes (forecast p (diagonal p)) (diagonal p) n = n)

/-- Reconstruct the existing rational update from the supplied finite past.
Its recursion follows the newest-first list, using each expert's prediction
before the corresponding feedback label. This is an adapter to the original
algorithm, not a second update or voting rule. -/
def historyWeights {N : ℕ} (experts : Fin N → Predictor) :
    List Bool → Fin N → ℚ
  | [] => fun _ => 1
  | b :: h => update (historyWeights experts h) (fun i => experts i h) b

def weighted {N : ℕ} (experts : Fin N → Predictor) (h : List Bool) : Bool :=
  predict (historyWeights experts h) (fun i => experts i h)

def advice {N : ℕ} (experts : Fin N → Predictor) (truth : ℕ → Bool)
    (n : ℕ) (i : Fin N) : Bool := experts i (past truth n)

/-- Exact agreement with the original learner on the SAME advice and truthful
feedback stream, for all finite pools and every actual stream and round. -/
def LearnerAdapter : Prop := ∀ (N : ℕ) (experts : Fin N → Predictor)
    (truth : ℕ → Bool) (n : ℕ),
  learner (advice experts truth) truth n = forecast (weighted experts) truth n

/-- Two-expert comparison at the shared horizon eleven: the original learner
makes eleven errors on its diagonal, so neither expert can satisfy the old
at-most-two-error hypothesis there. Feedback is exactly true. This specific
numerical consequence does not quantify over arbitrary pool sizes or budgets. -/
def TwoExpertComparison : Prop := ∀ experts : Fin 2 → Predictor,
  let truth := diagonal (weighted experts)
  (∀ n, mistakes (learner (advice experts truth) truth) truth n = n) ∧
  (∀ i : Fin 2, 2 < mistakes (fun t => advice experts truth t i) truth 11)

end TruthCore.Logic.AdaptivePrediction
