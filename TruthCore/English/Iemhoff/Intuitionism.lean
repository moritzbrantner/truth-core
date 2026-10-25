/-!
The intuitionist position on excluded middle, as reported by Rosalie Iemhoff,
"Intuitionism in the Philosophy of Mathematics", *Stanford Encyclopedia of
Philosophy* (Spring 2026 archive edition; substantive revision 2019), pinned as
the web snapshot `SEP-INTUITIONISM` (§3.1, §3.4 "Weak counterexamples", §6.3).

The encyclopedia reports the position of Brouwer, Heyting and Dummett; it is a
secondary witness, used because no primary witness is pinnable (source
`DUMMETT-EOI`). Each claim attributes the
position, not a view of the encyclopedia's author.

Vocabulary: `Stage` is the stages of the creating subject's knowledge;
`Proved s p` says that at stage `s` a proof of `p` is known; `Asserts s p` that
`p` is asserted at `s`. Propositions are Lean `Prop`s, so the reasoning *about*
these stages is itself constructive: nothing here or in the results built on it
uses `Classical.em`.
-/

namespace TruthCore.English.Iemhoff

universe u

/-- §3.1 (BHK-interpretation): "(A ∨ ¬A) holds intuitionistically if the
Creating Subject knows a proof of A or a proof that A cannot be proved". Only
the direction needed is taken: a proof of `p ∨ ¬p` at a stage is a proof of `p`
or of `¬p` at that stage (the BHK clause for disjunction, instantiated). -/
def ExcludedMiddleProvedOnlyWhenDecidedReading {Stage : Type u}
    (Proved : Stage → Prop → Prop) : Prop :=
  ∀ s p, Proved s (p ∨ ¬ p) → Proved s p ∨ Proved s (¬ p)

/-- §3.1: "In the case that neither for A nor for its negation a proof is
known, the statement (A ∨ ¬A) does not hold. The existence of open problems,
such as the Goldbach conjecture or the Riemann hypothesis, illustrates this
fact." Read as: at some stage some proposition is undecided. -/
def SomePropositionUndecidedReading {Stage : Type u}
    (Proved : Stage → Prop → Prop) : Prop :=
  ∃ s p, ¬ Proved s p ∧ ¬ Proved s (¬ p)

/-- §3.1, first sentence: "In intuitionism, knowing that a statement A is true
means having a proof of it." Read as the intuitionist norm of assertion: what is
asserted at a stage is proved at that stage. -/
def AssertionRequiresProofReading {Stage : Type u}
    (Proved Asserts : Stage → Prop → Prop) : Prop :=
  ∀ s p, Asserts s p → Proved s p

/-- §6.3 (Dummett): "the central notion in the theory of meaning for
mathematics is not, as in Platonism, truth, but proof". The intuitionist's
answer to "what makes a proposition true?", put in the place of a
proof-transcendent truth: a proposition holds exactly when it is proved at some
stage. This anti-realist biconditional is **not** attributed to the witness:
§6.3 states only the primacy of proof in the theory of meaning for mathematics
(`STMT-PROOF-NOT-TRUTH-CENTRAL-INTUITIONISM`, the claim's statement). Strengthening
it to a biconditional for every proposition is the comparison's own open premise
(`STMT-TRUTH-IS-PROVABILITY-INTUITIONISM`), outside the sourced `Intuitionist`
bundle (Codex P1 on #174). -/
def TruthIsProvabilityReading {Stage : Type u}
    (Proved : Stage → Prop → Prop) : Prop :=
  ∀ p : Prop, p ↔ ∃ s, Proved s p

end TruthCore.English.Iemhoff
