import TruthCore.Causality.EssentialPower

namespace TruthCore.Causality

/-- An upstream agent immediately lends power to its predecessor in a
reverse-natural-number chain. This is an abstract dependence relation,
not a claim that the links can exercise metaphysical efficient power. -/
def SuccessorBorrowingLink (upstream downstream : Nat) : Prop :=
  upstream = downstream + 1

/-- At finite truncation `depth`, the sole intrinsic source sits at that
boundary; at subsequent truncations its identity moves upstream. -/
def IntrinsicSourceAt (depth node : Nat) : Prop := node = depth

/-- Every fixed node eventually has a *finite derivation* from the source
of each sufficiently long finite chain. Yet the source of those chains
eventually leaves any fixed node or finite prefix of the chain.

The pointwise activity limit is the uniformly active successor chain,
which satisfies the local transmission equations even though no node is
intrinsic in the pointwise source limit. Under the already defined
`FinitelyGroundedPower` interpretation, that source-free limit cannot
ground node zero. This is a mathematical non-closure example, not a proof
that actual per se efficient power must use inductive grounding. -/
def FiniteGroundingNotClosedUnderEscapingSourceLimit : Prop :=
  (∀ node : Nat, ∃ cutoff : Nat, ∀ depth : Nat,
    cutoff ≤ depth →
      FinitelyGroundedPower SuccessorBorrowingLink
        (IntrinsicSourceAt depth) node) ∧
  (∀ node : Nat, ∃ cutoff : Nat, ∀ depth : Nat,
    cutoff ≤ depth → ¬ IntrinsicSourceAt depth node) ∧
  (∀ bound : Nat, ∃ depth : Nat, ∀ node : Nat,
    node ≤ bound → ¬ IntrinsicSourceAt depth node) ∧
  PowerTransmissionRule SuccessorBorrowingLink (fun _ => True) ∧
  ¬ FinitelyGroundedPower SuccessorBorrowingLink (fun _ => False) 0

end TruthCore.Causality
