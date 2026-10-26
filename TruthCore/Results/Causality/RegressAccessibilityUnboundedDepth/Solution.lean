import TruthCore.Causality.RegressReadings

namespace TruthCore.Results.Causality.RegressAccessibilityUnboundedDepth
open TruthCore.Causality

/-- Naturals under the predecessor link, plus a top (`none`) that every
natural links to. -/
def PredecessorWithTop : Option Nat → Option Nat → Prop
  | some k, some n => n = k + 1
  | some _, none => True
  | none, _ => False

private theorem accessibleSome (n : Nat) : Acc PredecessorWithTop (some n) := by
  induction n with
  | zero =>
    refine Acc.intro _ ?_
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some k => exact Nat.noConfusion hy
  | succ n ih =>
    refine Acc.intro _ ?_
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some k =>
      have hk : n = k := Nat.succ.inj hy
      exact hk ▸ ih

/-- Prepend a new top member to a chain. -/
private def prepend (top : Option Nat) (series : Nat → Option Nat) : Nat → Option Nat
  | 0 => top
  | i + 1 => series i

/-- A chain from `x` of length `length` becomes a chain
from `top` of length `length + 1` when `x` links to `top`. -/
private theorem prependChain {top x : Option Nat} {length : Nat}
    {series : Nat → Option Nat} (hLink : PredecessorWithTop x top)
    (hChain : DescendingPerSeChain PredecessorWithTop x length series) :
    DescendingPerSeChain PredecessorWithTop top (length + 1) (prepend top series) := by
  refine ⟨rfl, ?_⟩
  intro i hi
  cases i with
  | zero =>
    show PredecessorWithTop (series 0) top
    exact hChain.1 ▸ hLink
  | succ j => exact hChain.2 j (Nat.lt_of_succ_lt_succ hi)

/-- Below `some n` there is a chain of length `n`: `some n, some (n - 1), …,
some 0`. -/
private theorem chainFromSome (n : Nat) :
    ∃ series, DescendingPerSeChain PredecessorWithTop (some n) n series := by
  induction n with
  | zero => exact ⟨fun _ => some 0, rfl, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  | succ n ih =>
    obtain ⟨series, hChain⟩ := ih
    exact ⟨prepend (some (n + 1)) series, prependChain (x := some n) (rfl : n + 1 = n + 1) hChain⟩

/-- Every natural is accessible by induction, and the top is accessible because
all its causes are naturals. Below the top, `none, some (n - 1), …, some 0`
descends for `n` steps. No axiom is used. -/
theorem accessibilityAllowsUnboundedDepth :
    AccessibilityAllowsUnboundedDepth := by
  refine ⟨PredecessorWithTop, ?_, ?_⟩
  · intro x
    cases x with
    | some n => exact accessibleSome n
    | none =>
      refine Acc.intro _ ?_
      intro y hy
      cases y with
      | none => exact False.elim hy
      | some k => exact accessibleSome k
  · intro length
    cases length with
    | zero => exact ⟨fun _ => none, rfl, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
    | succ k =>
      obtain ⟨series, hChain⟩ := chainFromSome k
      exact ⟨prepend none series, prependChain (x := some k) trivial hChain⟩

end TruthCore.Results.Causality.RegressAccessibilityUnboundedDepth
