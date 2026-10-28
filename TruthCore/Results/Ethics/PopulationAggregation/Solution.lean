import TruthCore.Ethics.PopulationAggregation
import Mathlib.Tactic.NormNum

namespace TruthCore.Results.Ethics.PopulationAggregation
open TruthCore.Ethics.PopulationAggregation

/-- A finite Archimedean construction; it presupposes a common cardinal scale,
not a moral principle. No infinite population or infinite sum is used. -/
theorem lowMean (p : Profile) (ε : ℝ) (hε : 0 < ε) (_hLow : ε < p.mean) :
    ∃ q : Profile, q.mean = ε ∧ p.count < q.count ∧ p.total < q.total := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (p.total / ε) (p.count : ℝ))
  have hCountReal : (p.count : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hCount : p.count < m := by exact_mod_cast hCountReal
  have hTotal : p.total < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hm)
  exact ⟨⟨m, lt_trans p.nonempty hCount, ε⟩, rfl, hCount, hTotal⟩

/-- Finite arithmetic constraint; normative authority remains open. -/
theorem controls : Controls := by
  refine ⟨lowMean, ?_, ?_, ?_⟩
  · rintro ⟨r, ht, ha⟩
    let p : Profile := ⟨1, by decide, 2⟩
    obtain ⟨q, hq, _, htotal⟩ := lowMean p 1 (by norm_num) (by norm_num [p])
    have hmean := (ha p q).mp ((ht p q).mpr htotal)
    norm_num [p, hq] at hmean
  · intro p q hcount
    unfold Profile.total
    rw [hcount]
    have hpos : (0 : ℝ) < q.count := by exact_mod_cast q.nonempty
    exact mul_lt_mul_iff_right₀ hpos
  · intro p q hp hq
    have hz : q.total = 0 := by simp [Profile.total, hq]
    rw [hz]
    exact not_lt_of_ge (le_of_lt hp)

end TruthCore.Results.Ethics.PopulationAggregation
