module
public import TruthCore.Science.InductionSelection
public import TruthCore.Results.Science.PredicateRecoding.Solution
public import TruthCore.Results.Modern.Hume.Induction.Solution
@[expose] public section
namespace TruthCore.Results.Science.InductionSelection
open TruthCore.Science.InductionSelection

/-- Fixed inputs force invariant responses, so a singleton output must be a
fixed point. The proof needs no involutivity assumption beyond invertibility. -/
theorem symmetry : SymmetryConstraint := by
  intro E H r answer e hn hf
  have closed : ∀ h, answer e (r.hypothesis h) ↔ answer e h := by
    intro h
    simpa only [hf] using hn e h
  refine ⟨closed, ?_⟩
  intro h hs
  exact (hs (r.hypothesis h)).mp ((closed h).mpr ((hs h).mpr rfl))

theorem noUnique : NoUniqueSelector := by
  intro E H r select e hf hn hm
  apply hm
  exact (hn e).symm.trans (congrArg select hf)

private theorem flip_moves (b : Bool) : flip b ≠ b := by
  cases b <;> decide

private theorem alternatives : Alternatives := by
  refine ⟨fun _ => rfl, flip_moves, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rfl
  · intro h
    have bad := h ()
    cases bad
  · intro _ _
    rfl
  · intro _ _
    rfl
  · intro answer hn
    have same := (symmetry Unit Bool symmetric answer () hn rfl).1 false
    change answer () true ↔ answer () false at same
    by_cases h : answer () false
    · left
      intro b
      cases b with
      | false => exact h
      | true => exact same.mpr h
    · right
      intro b
      cases b with
      | false => exact h
      | true => exact fun ht => h (same.mp ht)

private theorem finiteInstantiation : FiniteInstantiation := by
  intro n
  have restrict : ∀ trace, record n (recodedTrace n trace) = record n trace := by
    intro trace
    funext i
    have hi : ¬ n ≤ i.val := Nat.not_le.mpr i.isLt
    simp [record, recodedTrace, hi, TruthCore.Science.PredicateRecoding.recode]
  have swap : ∀ h, recodedTrace n (prediction n h) = prediction n (!h) := by
    intro h
    funext i
    by_cases hi : i < n
    · have hn : ¬ n ≤ i := Nat.not_le.mpr hi
      simp [recodedTrace, prediction, hi, hn,
        TruthCore.Science.PredicateRecoding.recode]
    · have hn : n ≤ i := Nat.le_of_not_gt hi
      simp [recodedTrace, prediction, hi, hn,
        TruthCore.Science.PredicateRecoding.recode]
  have fit : ∀ h, compatible n (observed n) h := by
    intro h
    funext i
    simp [record, prediction, observed, i.isLt]
  have neutral : Neutral (finiteRecoding n) (compatible n) := by
    intro e h
    have same : record n (prediction n (!h)) = record n (prediction n h) := by
      rw [← swap h, restrict]
    change record n (prediction n (!h)) = e ↔ record n (prediction n h) = e
    rw [same]
  refine ⟨restrict, swap, fit, neutral, ?_, ?_, ?_, rfl⟩
  · simp [prediction]
  · intro answer hn h hs
    exact flip_moves h ((symmetry (Record n) Bool (finiteRecoding n)
      answer (observed n) hn rfl).2 h hs)
  · rintro ⟨select, hn⟩
    exact noUnique (Record n) Bool (finiteRecoding n) select (observed n)
      rfl hn (flip_moves _)

private theorem basisComparison : BasisComparison := by
  intro n hn
  have original : ∀ h, Uniform (prediction n h) ↔ h = true := by
    intro h
    constructor
    · intro hu
      have same := hu n 0
      simpa [prediction, hn] using same
    · intro hh
      subst h
      intro i j
      simp [prediction]
  refine ⟨original, ?_, ?_⟩
  · intro h
    rw [(finiteInstantiation n).2.1 h, original]
    cases h <;> decide
  · intro neutral
    have fixed := (symmetry (Record n) Bool (finiteRecoding n)
      (fun _ h => Uniform (prediction n h)) (observed n) neutral rfl).1 true
    have yes := (original true).mpr rfl
    have no := (original false).mp (fixed.mpr yes)
    cases no

/-- Symmetry obstruction with nonvacuous alternatives and observed-data model. -/
theorem certificate : Certificate :=
  ⟨TruthCore.Results.Science.PredicateRecoding.controls,
   TruthCore.Results.Modern.Hume.Induction.checks,
   symmetry, noUnique, alternatives, finiteInstantiation, basisComparison⟩
end TruthCore.Results.Science.InductionSelection
