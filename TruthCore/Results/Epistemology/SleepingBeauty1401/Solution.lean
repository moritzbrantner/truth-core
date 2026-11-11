module

public import TruthCore.Epistemology.SleepingBeauty1401
public import TruthCore.Results.Logic.CorrectionCriterion.Solution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section
namespace TruthCore.Results.Epistemology.SleepingBeauty1401
open TruthCore.Epistemology.SleepingBeauty1401

theorem incompatibility : Incompatibility := by
  have zero : ∀ a, N a → M a → a.t = 0 := by
    intro a hn hm
    have eq := (div_eq_iff (ne_of_gt hm.1)).mp hm.2
    dsimp [N] at hn
    linarith [a.normalized]
  refine ⟨zero, ?_, ?_, ?_⟩
  · intro a ⟨hn, hm, hp⟩
    have hz := zero a hn hm
    dsimp [P] at hp
    linarith
  · intro a ⟨hn, hm, hs⟩
    have hz := zero a hn hm
    dsimp [N] at hn
    dsimp [S] at hs
    linarith [a.normalized]
  · intro a hn hp
    dsimp [N] at hn
    dsimp [P] at hp
    have hd : 0 < a.h+a.m := by linarith [a.m_nonneg]
    apply (lt_div_iff₀ hd).mpr
    linarith [a.normalized]

theorem omissionControls : OmissionControls := by
  norm_num [OmissionControls, N, M, S, P, thirds, halves, zeroTuesday, headsGivenMonday]

theorem weightingAndWagers : WeightingAndWagers := by
  intro q
  have hk : (0:ℚ) < q.k := by exact_mod_cast q.k_pos
  have hk1 : (1:ℚ) ≤ q.k := by exact_mod_cast q.k_pos
  have hp := q.p_pos
  have hp1 := q.p_lt_one
  have ht : 0 < 1-q.p := by linarith
  have hd : 0 < awakeningNormalizer q := by
    dsimp [awakeningNormalizer]
    nlinarith
  have he : awakeningNormalizer q = 1 ↔ q.k = 1 := by
    dsimp [awakeningNormalizer]
    constructor
    · intro h
      have hkq : (q.k:ℚ) = 1 := by nlinarith
      exact_mod_cast hkq
    · intro h
      simp [h]
  have slot : slotHeads q = awakeningHeads q := by
    dsimp [slotHeads, awakeningHeads, awakeningNormalizer]
    have hden : 0 < q.p / q.k + (1-q.p) := by positivity
    field_simp
  refine ⟨slot, hd, div_pos hp hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_lt_one₀ hd).mpr
    dsimp [awakeningNormalizer]
    nlinarith
  · dsimp [awakeningHeads, experimentHeads]
    rw [div_eq_iff (ne_of_gt hd)]
    constructor
    · intro h
      apply he.mp
      nlinarith
    · intro h
      rw [he.mpr h]
      ring
  · intro h
    have hk2 : (1:ℚ) < q.k := by exact_mod_cast h
    apply (div_lt_iff₀ hd).mpr
    dsimp [awakeningNormalizer, experimentHeads]
    have : 1 < q.p + q.k * (1-q.p) := by nlinarith
    nlinarith
  · intro c
    dsimp [experimentGain]
    ring
  · intro c
    dsimp [awakeningGain, awakeningNormalizer]
    ring
  · intro c
    dsimp [experimentGain, experimentHeads]
    constructor <;> intro h <;> nlinarith
  · intro c
    dsimp [awakeningGain, awakeningHeads]
    rw [eq_div_iff (ne_of_gt hd)]
    dsimp [awakeningNormalizer]
    constructor <;> intro h <;> nlinarith

theorem appearanceBoundary : AppearanceBoundary := by
  intro h
  have inv := TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    Center Unit (fun _ => ()) (fun c => world c = .heads) |>.mp h
  have bad := (inv .headsMonday .tailsMonday rfl).mp rfl
  cases bad

end TruthCore.Results.Epistemology.SleepingBeauty1401
