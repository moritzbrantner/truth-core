import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Logic.ExcludedMiddleNotDeniable
open TruthCore.Logic
/-- Retorsion, formally: whoever denies an instance of excluded middle is
committed by that very denial to `¬p` and to `¬¬p`. Constructive, no
premises. -/
theorem denyingExcludedMiddleInstanceSelfContradictory :
    DenyingExcludedMiddleInstanceSelfContradictory := by
  intro p hDeny
  -- The denial yields ¬p: were p true, p ∨ ¬p would hold.
  have hNotP : ¬ p := fun hp => hDeny (Or.inl hp)
  -- The denial also yields ¬¬p: were ¬p true, p ∨ ¬p would hold.
  have hNotNotP : ¬ ¬ p := fun hnp => hDeny (Or.inr hnp)
  exact ⟨hNotP, hNotNotP⟩

/-- No instance of excluded middle can be consistently denied. This refutes the
*denial* of excluded middle for any single proposition. It does not refute
*withholding* assent from `p ∨ ¬p` (the intuitionist's actual position), and it
does not prove excluded middle. -/
theorem noExcludedMiddleInstanceDeniable : NoExcludedMiddleInstanceDeniable := by
  intro ⟨p, hDeny⟩
  -- The denier of this instance is committed to ¬p and to ¬¬p.
  have hBoth := denyingExcludedMiddleInstanceSelfContradictory p hDeny
  exact hBoth.2 hBoth.1
end TruthCore.Results.Logic.ExcludedMiddleNotDeniable
