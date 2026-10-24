/-!
Excluded middle and its constructive neighbours (#167).

`ExcludedMiddle` is the general principle that the root path uses in at least
two instances (`TruthCore.Case.Catholicism.FirstUnmovedMoverExistsOrNot` and
`TruthCore.Case.Catholicism.FirstUnmovedMoversIdenticalOrDistinct`). It is
stated here as a proposition, never assumed as an axiom: Lean's
`Classical.em` is not used anywhere in this module or in the results that
build on it, and every such result is checked with `permitted_axioms: []`.

What Lean can and cannot show about it, without any axiom:

* every instance is irrefutable, `∀ p, ¬¬(p ∨ ¬p)`
  (`ExcludedMiddleIrrefutable`);
* hence no instance can be consistently denied
  (`NoExcludedMiddleInstanceDeniable`);
* excluded middle is equivalent to double-negation elimination
  (`ExcludedMiddleIffDoubleNegationElimination`);
* it does **not** prove `ExcludedMiddle` itself. That is the intuitionist's
  point, and it is why the self-evidence of `STMT-EXCLUDED-MIDDLE` is argued
  (Aristotle's elenchus, *Metaphysics* IV.4 and IV.7, plus the results above),
  not proved.
-/

namespace TruthCore.Logic

universe u

/-- Excluded middle as a general principle: every proposition either holds or
does not hold.

Source reading: Aristotle, *Metaphysics* IV.7, 1011b23-24: "there cannot be
anything between the two sides of a contradiction, but of one subject one must
either affirm or deny any one predicate"; read with 1011b25-29 (to say of what
is that it is, or of what is not that it is not, is true) as a thesis about how
things are, not about what a speaker must actually utter. Aristotle states it
for predication ("one of one"); `excludedMiddle_iff_predicative` shows that the
predicative form over arbitrary subjects and predicates is equivalent, so the
propositional form is not a strengthening. -/
def ExcludedMiddle : Prop :=
  ∀ p : Prop, p ∨ ¬ p

/-- Double-negation elimination: whatever cannot be false is true. -/
def DoubleNegationElimination : Prop :=
  ∀ p : Prop, ¬ ¬ p → p

/-- Every instance of excluded middle is irrefutable: its negation leads to
contradiction. Constructively provable; strictly weaker than
`ExcludedMiddle`. -/
def ExcludedMiddleIrrefutable : Prop :=
  ∀ p : Prop, ¬ ¬ (p ∨ ¬ p)

/-- Denial of excluded middle for some proposition: there is a `p` such that
neither `p` nor `¬p`. The position Aristotle ascribes to Anaxagoras'
mixture, "something between the contradiction" (*Metaphysics* IV.7,
1012a24-28). Recorded as an alternative to `ExcludedMiddle`; it is the negation
of `NoExcludedMiddleInstanceDeniable`. -/
def SomeExcludedMiddleInstanceFails : Prop :=
  ∃ p : Prop, ¬ (p ∨ ¬ p)

/-- No instance of excluded middle can be consistently denied: there is no
proposition `p` of which one may hold that neither `p` nor `¬p`. This is the
retorsion point, and only that: it excludes *denying* an instance, not
*withholding* assent from it. -/
def NoExcludedMiddleInstanceDeniable : Prop :=
  ¬ SomeExcludedMiddleInstanceFails

/-- Whoever denies an instance of excluded middle is thereby committed to a
contradiction of the form `¬p ∧ ¬¬p`: the denial itself yields `¬p` (were `p`
true, so would be `p ∨ ¬p`) and `¬¬p` (were `¬p` true, likewise). -/
def DenyingExcludedMiddleInstanceSelfContradictory : Prop :=
  ∀ p : Prop, ¬ (p ∨ ¬ p) → ¬ p ∧ ¬ ¬ p

/-- Excluded middle and double-negation elimination are equivalent. -/
def ExcludedMiddleIffDoubleNegationElimination : Prop :=
  ExcludedMiddle ↔ DoubleNegationElimination

/-- The predicative form of *Metaphysics* IV.7, 1011b23-24 ("of one subject one
must either affirm or deny any one predicate"), over subjects of any type. -/
def PredicativeExcludedMiddle : Prop :=
  ∀ (α : Sort u) (P : α → Prop) (s : α), P s ∨ ¬ P s

/-- The predicative and propositional forms are equivalent, constructively:
every proposition is a predication about a trivial subject, and every
predication is a proposition. Supports the fidelity note on `ExcludedMiddle`;
not itself an advertised result. -/
theorem excludedMiddle_iff_predicative :
    ExcludedMiddle ↔ PredicativeExcludedMiddle.{u} := by
  constructor
  · intro hEM α P s
    exact hEM (P s)
  · intro hPred p
    exact hPred PUnit (fun _ => p) PUnit.unit

/-- Intuitionist withholding of excluded middle (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`),
over stages `Stage` of knowledge with `Proved s p` (a proof of `p` is known at
`s`) and `Asserts s p` (`p` is asserted at `s`):

1. `p ∨ ¬p` is asserted at a stage only when `p` or `¬p` is proved there;
2. at some stage some instance `p ∨ ¬p` is not asserted (assent withheld);
3. withholding is not denial: every denial `¬(p ∨ ¬p)` is refuted.

It is a position about assertion, not a proposition `¬ ExcludedMiddle`. Derived
from the intuitionist theory's commitments in
`INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD`. -/
def ExcludedMiddleWithheld {Stage : Type u} (Proved Asserts : Stage → Prop → Prop) : Prop :=
  (∀ s p, Asserts s (p ∨ ¬ p) → Proved s p ∨ Proved s (¬ p)) ∧
    (∃ s p, ¬ Asserts s (p ∨ ¬ p)) ∧
    ExcludedMiddleIrrefutable

end TruthCore.Logic
