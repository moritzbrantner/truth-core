import TruthCore.Causality.GroundingLimits
import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution

namespace TruthCore.Results.Causality.FiniteGroundingLimitNotClosed
open TruthCore.Causality

/-- Build an actual inductive power certificate by transferring it across
`steps` links from the intrinsically powered last node. -/
private theorem groundedAfterSteps (steps : Nat) :
    ∀ start : Nat,
      FinitelyGroundedPower SuccessorBorrowingLink
        (IntrinsicSourceAt (start + steps)) start := by
  induction steps with
  | zero =>
    intro start
    exact FinitelyGroundedPower.intrinsic start rfl
  | succ steps ih =>
    intro start
    refine FinitelyGroundedPower.borrowed (y := start + 1) ?_ ?_
    · rfl
    · have hGround := ih (start + 1)
      have hEndpoint : (start + 1) + steps = start + (steps + 1) := by
        calc
          (start + 1) + steps = start + (1 + steps) := Nat.add_assoc start 1 steps
          _ = start + (steps + 1) :=
            congrArg (fun k : Nat => start + k) (Nat.add_comm 1 steps)
      exact hEndpoint ▸ hGround

/-- Pointwise stabilization of *activity* from successively remote sources
does not imply stabilization of any intrinsic source. The final all-on
assignment is a valid local fixed point, but source-free inductive grounding
is ruled out by the existing `FINITE-GROUNDING-HAS-SOURCE` result. -/
theorem finiteGroundingLimitNotClosed :
    FiniteGroundingNotClosedUnderEscapingSourceLimit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro node
    refine ⟨node, ?_⟩
    intro depth hNode
    have hEndpoint : node + (depth - node) = depth := by
      calc
        node + (depth - node) = (depth - node) + node := Nat.add_comm _ _
        _ = depth := Nat.sub_add_cancel hNode
    have hGround := groundedAfterSteps (depth - node) node
    exact hEndpoint ▸ hGround
  · intro node
    refine ⟨node + 1, ?_⟩
    intro depth hDepth hSource
    have hBefore : node < depth :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self node) hDepth
    exact (Nat.ne_of_lt hBefore) hSource
  · intro bound
    refine ⟨bound + 1, ?_⟩
    intro node hBelow hSource
    have hImpossible : bound + 1 ≤ bound := by
      calc
        bound + 1 = node := hSource.symm
        _ ≤ bound := hBelow
    exact (Nat.not_succ_le_self bound) hImpossible
  · intro node
    constructor
    · intro _
      exact ⟨node + 1, rfl, trivial⟩
    · intro _
      trivial
  · intro hGrounded
    obtain ⟨source, _path, hIntrinsic⟩ :=
      TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource
        Nat SuccessorBorrowingLink (fun _ => False) 0 hGrounded
    exact hIntrinsic

end TruthCore.Results.Causality.FiniteGroundingLimitNotClosed
