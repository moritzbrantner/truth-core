import TruthCore.Epistemology.UltimateExplanation
namespace TruthCore.Results.Epistemology.UltimateExplanation
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Modern.Hume.Regularity

private theorem stableCell (n : Nat) : Cell stable on n on :=
  ⟨⟨rfl, fun _ => rfl⟩, fun _ _ => rfl⟩

private theorem stableTrace (f : Trace) (h : Follows stable f) (t : Nat) :
    f t = true := by
  induction t with
  | zero => exact h.1
  | succ t ih => exact (h.2 t).trans ih

private theorem stableAccurate (n : Nat) : Accurate stable on n := by
  intro f hf
  exact (stableTrace f hf.1 (n+1)).symm

private theorem trueBest (b : Action) : payoff b true ≤ payoff .betTrue true := by
  cases b <;> decide

private theorem stableOptimal (n : Nat) : Optimal stable on n .betTrue := by
  intro f hf b
  rw [stableTrace f hf.1 (n+1)]
  exact trueBest b

private theorem openCell (n : Nat) : Cell (openFuture n) on n on :=
  ⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩

private theorem badCell (n : Nat) : Cell (openFuture n) on n (delayedFailure (n+1)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ite_eq_left (Nat.zero_lt_succ n)
  · intro t ht
    rw [delayedFailure, ite_eq_left ht, delayedFailure, ite_eq_left (Nat.lt_of_succ_lt ht)]
  · intro i hi
    exact ite_eq_left hi

private theorem badNext (n : Nat) : delayedFailure (n+1) (n+1) = false :=
  ite_eq_right (Nat.lt_irrefl _)

private theorem inaccurate (n : Nat) : ¬ Accurate (openFuture n) on n := by
  intro h
  have he := h _ (badCell n)
  rw [badNext] at he
  exact Bool.noConfusion he

private theorem noOptimal (n : Nat) : ¬ ∃ a, Optimal (openFuture n) on n a := by
  rintro ⟨a, ha⟩
  cases a with
  | safe => have h := ha on (openCell n) .betTrue; exact (by decide : ¬ 2 ≤ 1) h
  | betTrue =>
    have h := ha _ (badCell n) .betFalse
    rw [badNext] at h
    exact (by decide : ¬ 2 ≤ 0) h
  | betFalse => have h := ha on (openCell n) .betTrue; exact (by decide : ¬ 2 ≤ 0) h

/-- Populated rival continuations and substantive source-independent model
comparison; imported Hume certificates remain consequences, not source truths. -/
theorem certificate : Certificate := by
  have boundary := TruthCore.Results.Modern.Hume.Regularity.checks.2.2.2.2.2.2.2.1
  have stableTests : ∀ n, Cell stable on n on ∧ Accurate stable on n ∧
      Optimal stable on n .betTrue := fun n =>
    ⟨stableCell n, stableAccurate n, stableOptimal n⟩
  refine ⟨TruthCore.Results.Modern.Hume.Induction.checks,
    TruthCore.Results.Modern.Hume.Regularity.checks,
    ⟨boundary.1.1, boundary.1.2, boundary.2.1.1, boundary.2.1.2.1⟩,
    ?_, stableTests, ?_, ?_, ?_, ?_, ?_⟩
  · intro t a b c hb hc
    exact hb.trans hc.symm
  · intro _ n _; exact stableTests n
  · intro n
    refine ⟨openCell n, badCell n, inaccurate n, ?_, noOptimal n⟩
    intro _ _; exact Nat.le_refl 1
  · intro n; exact ⟨boundary.2.1.2.1, inaccurate n⟩
  · intro n
    exact ⟨fun _ _ => rfl, fun _ hi => ite_eq_left hi⟩
  · intro n
    refine ⟨?_, delayedFailure (n+1), badCell n, ?_⟩
    · intro f hf
      exact ⟨⟨hf.1.1, fun t _ => hf.1.2 t⟩, hf.2⟩
    · intro h
      have he := stableTrace _ h.1 (n+1)
      rw [badNext] at he
      exact Bool.noConfusion he

theorem omissions : Omissions := by
  have empty : ¬ ∃ f, Cell (⟨false, stable.step⟩ : Profile) on 0 f := by
    rintro ⟨f, hf⟩
    have he := hf.2 0 (Nat.zero_lt_succ 0)
    have hf0 := hf.1.1
    exact Bool.noConfusion (hf0.symm.trans he)
  refine ⟨⟨empty, ?_, ?_⟩, ⟨⟨.process, trivial⟩, ⟨rfl, fun _ => rfl⟩,
    Bool.noConfusion⟩, ?_⟩
  · intro f hf; exact (empty ⟨f, hf⟩).elim
  · intro f hf; exact (empty ⟨f, hf⟩).elim
  · constructor
    · intro t a b c hb hc; exact hb.trans hc.symm
    · intro h; exact Bool.noConfusion (h.2 0)
end TruthCore.Results.Epistemology.UltimateExplanation

namespace TruthCore.Results.Epistemology.UltimateExplanation
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.HistoryContrastive

private theorem occupied (w : Bool) : occupancy w = on := by
  cases w <;> rfl

private theorem projected : globalObservation fixedSignal = on := rfl

/-- Composes #736 directly: same observed stream, opposed whole-history
selection verdict, and certified unique global constraints. -/
theorem integration : Integration := by
  have old := TruthCore.Results.Explanation.HistorySelection.certificate
  refine ⟨old, ?_, ?_, ?_, ?_⟩
  · exact TruthCore.Results.Explanation.HistorySelection.no_selection chains
      (reasons false).reasonPresent (fun _ => True) false true trivial
      distinct_histories (fun _ _ => Iff.rfl)
  · intro hs
    exact TruthCore.Results.Explanation.HistorySelection.rooted_failure
      ((TruthCore.Results.Explanation.HistorySelection.characterization rooted
        (reasons false).reasonPresent (fun _ => True) false).mpr hs)
  · intro w n
    refine ⟨?_, ?_, ?_, Iff.rfl, Iff.rfl⟩
    · rw [occupied]; exact stableCell n
    · rw [occupied]; exact stableAccurate n
    · rw [occupied]; exact stableOptimal n
  · intro signal hs n
    have eq := old.2.2.2.1.2 signal hs
    subst signal
    rw [projected, occupied]
    exact ⟨rfl, stableCell n, stableAccurate n, stableOptimal n⟩
end TruthCore.Results.Epistemology.UltimateExplanation
