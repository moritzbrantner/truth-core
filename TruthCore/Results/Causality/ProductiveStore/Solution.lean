module
public import TruthCore.Causality.ProductiveStore
@[expose] public section
namespace TruthCore.Results.Causality.ProductiveStore
open TruthCore.Causality.ProductiveStore

theorem budget : Budget := by
  intro m h
  rcases h with ⟨_, ha, _, _, _, hb⟩
  constructor
  · linarith
  · intro hn hp
    linarith

theorem controls : Controls := by
  norm_num [Controls, Admissible]

theorem temporalBudget : TemporalBudget := by
  intro stock input output hn hb n
  have eqn : ∀ n, stock n + (∑ t ∈ Finset.range n, output t) =
      stock 0 + ∑ t ∈ Finset.range n, input t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      have := hb n
      linarith
  have := eqn n
  have := hn n
  linarith
theorem decayingDischarge : DecayingDischarge := by
  intro n
  dsimp
  have hp : (0:ℝ) < (1/2)^n := pow_pos (by norm_num) _
  constructor
  · simp only [Admissible, pow_succ]
    exact ⟨by positivity, by positivity, le_rfl, by positivity, by positivity, by ring⟩
  · positivity
end TruthCore.Results.Causality.ProductiveStore
