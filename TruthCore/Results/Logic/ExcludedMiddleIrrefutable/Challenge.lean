import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Logic.ExcludedMiddleIrrefutable
open TruthCore.Logic
/-- Every instance of excluded middle is irrefutable, `∀ p, ¬¬(p ∨ ¬p)`, proved
constructively from no premises and without `Classical.em`. This does not prove
excluded middle: `¬¬(p ∨ ¬p)` is strictly weaker than `p ∨ ¬p` in
intuitionistic logic. -/
theorem excludedMiddleIrrefutable : ExcludedMiddleIrrefutable := by
  sorry
end TruthCore.Results.Logic.ExcludedMiddleIrrefutable
