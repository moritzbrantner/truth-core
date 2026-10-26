import TruthCore.Causality.GroundingRegress

namespace TruthCore.Results.Causality.GroundingAllowsRegress
open TruthCore.Causality TruthCore.Causality.GroundingRegress

/-- The links: `none` causes every `some n`, and `some (n + 1)` causes
`some n`. -/
def link : Option Nat → Option Nat → Prop
  | none, some _ => True
  | some m, some n => m = n + 1
  | _, none => False

/-- Model: the single intrinsic source is `none`. Every `some n` borrows
directly from it, and `none` receives no link. The descending chain
`some 0 ← some 1 ← …` still makes `some 0` inaccessible. -/
theorem groundingWithoutUniqueCauseAllowsRegress :
    GroundingWithoutUniqueCauseAllowsRegress := by
  refine ⟨link, fun x => x = none, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | none => exact .intrinsic none rfl
    | some n => exact .borrowed (y := none) trivial (.intrinsic none rfl)
  · intro x hx y hy
    subst hx
    cases y <;> exact hy
  · intro hAccessible
    have notAcc : ∀ n, ¬ Acc link (some n) := by
      intro n hAcc
      generalize hx : some n = x at hAcc
      induction hAcc generalizing n with
      | intro x _ ih => subst hx; exact ih (some (n + 1)) rfl (n + 1) rfl
    exact notAcc 0 (hAccessible (some 0))

end TruthCore.Results.Causality.GroundingAllowsRegress
