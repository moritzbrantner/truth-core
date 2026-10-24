import TruthCore.Logic.ExcludedMiddle
import TruthCore.English.Iemhoff.Intuitionism

/-!
Intuitionism as a rival theory to the self-evident `STMT-EXCLUDED-MIDDLE`
(#143, owner decisions of 2026-10-23 and 2026-10-24): not "classical logic minus
one axiom", but a theory that puts its own account of truth and assertion in
the place of excluded middle, answers the shared questions, and records what it
leaves unexplained.

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.

## Answer map

Each line names the proposition that answers the question, or *unexplained*.

* **Q-EXCLUDED-MIDDLE** (does every proposition either hold or not?).
  Aristotelian/Catholic: yes, `STMT-EXCLUDED-MIDDLE` (self-evident, #167).
  Intuitionist: withheld, `STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`, derived
  from the commitments below (`INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD`);
  not denied, `STMT-EXCLUDED-MIDDLE-IRREFUTABLE`.
* **Q-TRUTH** (what makes a proposition or a thought true?).
  Aristotelian: a thought is true when it combines as things are,
  `STMT-THOUGHT-TRUE-OR-FALSE-BY-COMPOSITION` (*Met.* IV.7, 1012a4-5 with
  1011b26-27). Intuitionist: being proved at some stage,
  `STMT-TRUTH-IS-PROVABILITY-INTUITIONISM` (recorded as an alternative to the
  Aristotelian premise).
* **Q-FIRST-MOVER** (the regress: is there a first unmoved mover?).
  Catholic: yes, via the prima via and the excluded-middle instance
  `STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT`. Intuitionist: the prima via result
  itself is constructive (`AQUINAS-ST-I-Q2-A3-PRIMA-VIA`, `permitted_axioms: []`),
  so the intuitionist who grants its premises grants
  `STMT-FIRST-UNMOVED-MOVER-CANNOT-BE-LACKING` (`¬¬∃`). The step to "there is
  one" uses the excluded-middle instance, which is withheld until the question
  is decided. Whether there is a first mover, and so what originates motion, is
  **unexplained**.
* **Q-ONE-FIRST-MOVER** (are any two first movers the same?). Catholic: yes,
  via the instance `STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT` (ST I q.11
  a.3). Intuitionist: the instance is withheld unless identity of first movers
  is decidable: **unexplained**.
* **Q-DECIDABLE-CASES**: agreement. Aristotle's example of number (*Met.* IV.7,
  1012a9-12, odd or not odd) is decidable, so the intuitionist grants it.
* **Q-CHANGE** (*Met.* IV.7, 1011b29-1012a1): the intuitionist grants the
  derivation (`ARIST-MET-1011B-1012A-CHANGE-DECIDES-CONTRADICTORY-PAIR` is
  constructive) but withholds its change premise for any pair not already
  decided, since that premise is a disjunction about every change.
* **Existence, cosmic order, mind, morality, the historical evidence about
  Jesus and the Church**: intuitionism is a theory of logic, truth and
  mathematical meaning; it gives no answer of its own. **Unexplained**, until it
  is paired with a full worldview (an owner decision; Dummett himself was a
  Catholic).
-/

namespace TruthCore.Comparison.ExcludedMiddle

open TruthCore.Logic
open TruthCore.English.Iemhoff

/-- The shared signature: stages of knowledge, their order, what is proved and
what is asserted at a stage. -/
structure Sig where
  Stage : Type
  Proved : Stage → Prop → Prop
  Asserts : Stage → Prop → Prop

/-- The intuitionist theory's commitments in this question set, as one flat
conjunction so that `bind-check` binds each to its statement (all from the
pinned SEP witness, `SEP-INTUITIONISM`):
1. `p ∨ ¬p` is proved only when `p` or `¬p` is (§3.1);
2. some proposition is undecided at some stage (§3.1, open problems);
3. assertion requires proof (§3.1);
4. no instance of excluded middle can be refuted, `∀ p, ¬¬(p ∨ ¬p)` (§3.4);
5. truth is provability, the account put in place of excluded middle (§6.3).
-/
def Intuitionist (s : Sig) : Prop :=
  ExcludedMiddleProvedOnlyWhenDecidedReading s.Proved ∧
    SomePropositionUndecidedReading s.Proved ∧
    AssertionRequiresProofReading s.Proved s.Asserts ∧
    ExcludedMiddleIrrefutable ∧
    TruthIsProvabilityReading s.Proved

/-- The intuitionist theory is consistent: some interpretation of the shared
signature satisfies all its commitments. -/
def IntuitionistTheoryConsistent : Prop :=
  ∃ s : Sig, Intuitionist s

end TruthCore.Comparison.ExcludedMiddle
