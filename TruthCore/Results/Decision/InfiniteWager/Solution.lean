import TruthCore.Decision.InfiniteWager

namespace TruthCore.Results.Decision.InfiniteWager
open TruthCore.Decision.InfiniteWager

theorem mixtureTie : MixtureTie := by
  have ht : ∀ p q : ENNReal, p ≠ 0 → q ≠ 0 → value p q = ⊤ := by
    intro p q hp hq
    simp [value, hp, hq]
  refine ⟨ht, ?_, ?_, ?_⟩
  · intro p hp
    constructor
    · rw [ht p 1 hp (by simp), ht p (1 / 2) hp (by simp)]
    · exact ne_of_gt (by simp)
  · intro q
    simp [value]
  · intro p
    simp [value]

end TruthCore.Results.Decision.InfiniteWager
