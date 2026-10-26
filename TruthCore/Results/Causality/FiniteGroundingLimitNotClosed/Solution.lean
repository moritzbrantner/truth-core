import TruthCore.Causality.GroundingLimits
import TruthCore.Results.Causality.FiniteGroundingHasSource.Solution

namespace TruthCore.Results.Causality.FiniteGroundingLimitNotClosed
open TruthCore.Causality

/-- Extending a finite chain by one upstream intrinsic source preserves
each previous finite grounding certificate, but changes its source. -/
private theorem extendIntrinsicSource (depth : Nat) {node : Nat}
    (grounded : FinitelyGroundedPower SuccessorBorrowingLink
      (IntrinsicSourceAt depth) node) :
    FinitelyGroundedPower SuccessorBorrowingLink
      (IntrinsicSourceAt (depth + 1)) node := by
  induction grounded with
  | intrinsic x hIntrinsic =>
    refine FinitelyGroundedPower.borrowed (y := x + 1) ?_ ?_
    · rfl
    · exact FinitelyGroundedPower.intrinsic (x + 1)
        (congrArg (fun k : Nat => k + 1) hIntrinsic)
  | borrowed hLink _ ih =>
    exact FinitelyGroundedPower.borrowed hLink ih

/-- Induct directly on the finite-depth inclusion witness, avoiding
any appeal to limit preservation or arithmetic normalization. -/
private theorem groundedUpToDepth (node depth : Nat) (within : node ≤ depth) :
    FinitelyGroundedPower SuccessorBorrowingLink
      (IntrinsicSourceAt depth) node := by
  induction within with
  | refl =>
    exact FinitelyGroundedPower.intrinsic node rfl
  | step _ ih =>
    exact extendIntrinsicSource _ ih

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
    exact groundedUpToDepth node depth hNode
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
