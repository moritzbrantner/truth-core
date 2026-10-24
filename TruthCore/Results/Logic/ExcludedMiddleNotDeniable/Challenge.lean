import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Logic.ExcludedMiddleNotDeniable
open TruthCore.Logic
/-- Retorsion, formally: whoever denies an instance of excluded middle is
committed by that very denial to `¬p` and to `¬¬p`. Constructive, no
premises. -/
theorem denyingExcludedMiddleInstanceSelfContradictory :
    DenyingExcludedMiddleInstanceSelfContradictory := by
  sorry

/-- No instance of excluded middle can be consistently denied. This refutes the
*denial* of excluded middle for any single proposition. It does not refute
*withholding* assent from `p ∨ ¬p` (the intuitionist's actual position), and it
does not prove excluded middle. -/
theorem noExcludedMiddleInstanceDeniable : NoExcludedMiddleInstanceDeniable := by
  sorry
end TruthCore.Results.Logic.ExcludedMiddleNotDeniable
