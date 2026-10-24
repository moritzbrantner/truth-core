import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Logic.ExcludedMiddleIrrefutable
open TruthCore.Logic
/-- Every instance of excluded middle is irrefutable, `∀ p, ¬¬(p ∨ ¬p)`, proved
constructively from no premises and without `Classical.em`. This does not prove
excluded middle: `¬¬(p ∨ ¬p)` is strictly weaker than `p ∨ ¬p` in
intuitionistic logic. -/
theorem excludedMiddleIrrefutable : ExcludedMiddleIrrefutable := by
  intro p hDeny
  -- Were p true, the denied disjunction would hold by its left side.
  have hNotP : ¬ p := fun hp => hDeny (Or.inl hp)
  -- So ¬p holds, and the denied disjunction holds by its right side.
  exact hDeny (Or.inr hNotP)
end TruthCore.Results.Logic.ExcludedMiddleIrrefutable
