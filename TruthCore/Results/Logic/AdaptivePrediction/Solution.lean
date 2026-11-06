module

public import TruthCore.Logic.AdaptivePrediction
public import TruthCore.Results.Logic.FallibleCorrection.Solution

@[expose] public section
namespace TruthCore.Results.Logic.AdaptivePrediction
open TruthCore.Logic.AdaptivePrediction
open TruthCore.Logic.FallibleCorrection

private theorem history_eq (p : Predictor) (n : ℕ) :
    history p n = past (diagonal p) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change diagonal p n :: history p n = diagonal p n :: past (diagonal p) n
    rw [ih]

private theorem wrong (p : Predictor) (n : ℕ) :
    forecast p (diagonal p) n ≠ diagonal p n := by
  unfold forecast
  rw [← history_eq]
  unfold diagonal
  cases p (history p n) <;> intro h <;> cases h

/-- One coherent adversarial stream, uniformly across every horizon. -/
theorem diagonalBoundary : DiagonalBoundary := by
  intro p
  refine ⟨history_eq p, wrong p, ?_⟩
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mistakes, ite_eq_right (wrong p n), ih]

private theorem weights_eq {N : ℕ} (experts : Fin N → Predictor)
    (truth : ℕ → Bool) (n : ℕ) :
    weights (advice experts truth) truth n = historyWeights experts (past truth n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change update (weights (advice experts truth) truth n)
      (advice experts truth n) (truth n) =
      update (historyWeights experts (past truth n))
        (fun i => experts i (past truth n)) (truth n)
    rw [ih]
    rfl

/-- The history adapter preserves the original learner's complete finite trace. -/
theorem learnerAdapter : LearnerAdapter := by
  intro N experts truth n
  unfold learner forecast weighted
  rw [weights_eq]
  rfl

private theorem learner_count {N : ℕ} (experts : Fin N → Predictor) (n : ℕ) :
    let truth := diagonal (weighted experts)
    mistakes (learner (advice experts truth) truth) truth n = n := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mistakes, learnerAdapter]
    rw [ite_eq_right (wrong (weighted experts) n), ih]

private theorem truthful_count (truth : ℕ → Bool) (n : ℕ) :
    mistakes truth truth n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mistakes, ite_eq_left rfl, ih]

/-- Compose the old positive budget with the SAME learner and true feedback.
At this horizon no expert can meet that budget; the positive theorem survives. -/
theorem twoExpertComparison : TwoExpertComparison := by
  intro experts
  dsimp only
  refine ⟨learner_count experts, ?_⟩
  intro i
  apply Nat.lt_of_not_ge
  intro he
  have budget := TruthCore.Results.Logic.FallibleCorrection.certificate.2.2.1
  have h := budget (advice experts (diagonal (weighted experts)))
    (diagonal (weighted experts)) (diagonal (weighted experts)) 11 i he
    (by rw [truthful_count]; exact Nat.zero_le 1)
  rw [learner_count] at h
  exact Nat.not_succ_le_self 10 h

end TruthCore.Results.Logic.AdaptivePrediction
