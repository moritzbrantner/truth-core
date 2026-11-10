module
public import TruthCore.Results.Causality.ProductiveStore.Solution
@[expose] public section
namespace TruthCore.Results.Causality.ProductiveSustained
open TruthCore.Causality.ProductiveStore
open TruthCore.Results.Causality.ProductiveStore

theorem uniformBudget : UniformBudget := by
  intro stock output ε hs hb hl n
  have ht := temporalBudget stock (fun _ => 0) output hs (by simpa using hb) n
  have hsum : (n : ℝ)*ε ≤ ∑ t ∈ Finset.range n, output t := by
    calc
      (n : ℝ)*ε = ∑ _t ∈ Finset.range n, ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hl t)
  simpa using le_trans hsum ht

theorem noUniformDischarge : NoUniformDischarge := by
  intro stock output ε hs hb hp hl
  obtain ⟨n, hn⟩ := exists_nat_gt (stock 0 / ε)
  have hgt : stock 0 < (n : ℝ)*ε := (div_lt_iff₀ hp).mp hn
  have hle := uniformBudget stock output ε hs hb hl n
  linarith

theorem decayingNoUniform : DecayingNoUniform := by
  rintro ⟨ε, hp, hl⟩
  apply noUniformDischarge (fun n => 2*(1/2)^n) (fun n => (1/2)^n) ε
    (fun n => by positivity) (fun n => by simp only [pow_succ]; ring) hp hl

theorem replenishedUniform : ReplenishedUniform := by
  intro _
  norm_num [Admissible]
end TruthCore.Results.Causality.ProductiveSustained
