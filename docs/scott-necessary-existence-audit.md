# Necessary existence in the Scott and Gödel 1970 embeddings

Working comparison for [existence phase B, #274](https://github.com/moritzbrantner/truth-core/issues/274). Source witnesses are the pinned AFP [Scott `GoedelGod.thy`](../corpus/passages/afp-goedelgod.json) and [Gödel 1970 `GoedelVariantHOML1.thy`](../corpus/passages/afp-notes-goedel-homl1.json). They document *formalizations*, not unpinned original manuscript intentions.

## Separately established results

| Result | Verdict | Exact scope |
| --- | --- | --- |
| [`SCOTT-GOD-LIKE-NECESSARILY-EXISTS`](../corpus/results/SCOTT-GOD-LIKE-NECESSARILY-EXISTS.json) | Derived conditionally | Scott T3 from A1a, A1b, A2, A3, A4, **A5**, symmetry and excluded middle. A5 and the other premises are not proved true. |
| [`SCOTT-A5-INDEPENDENCE`](../corpus/results/SCOTT-A5-INDEPENDENCE.json) | Countermodel | A1a–A4 do not entail A5 (or T3); a finite S5 model satisfies them without A5. This does not show A5 is false. |
| [`SCOTT-NE-WORLD-ISOLATION`](../corpus/results/SCOTT-NE-WORLD-ISOLATION.json) | Derived without positivity axioms | With *all* intensional properties admissible, `NE x w` holds iff every world accessible from `w` equals `w`. The world-indexed singleton property is admissible under full comprehension. |
| [`SCOTT-NE-FULL-FILTER-AGREEMENT`](../corpus/results/SCOTT-NE-FULL-FILTER-AGREEMENT.json) | Derived without axioms | A stipulated property filter on **both** essence and necessary-existence quantifiers reproduces Scott's definitions when all properties are admitted. |
| [`SCOTT-NE-INVARIANT-FILTER-TRIVIAL`](../corpus/results/SCOTT-NE-INVARIANT-FILTER-TRIVIAL.json) | Derived without axioms | With only world-invariant properties admissible in both quantifiers, every bearer satisfies filtered NE under the same possibilist, constant-domain embedding. This does not prove actualist existence. |
| [`SCOTT-NE-INVARIANT-FILTER-COUNTERMODEL`](../corpus/results/SCOTT-NE-INVARIANT-FILTER-COUNTERMODEL.json) | Countermodel | In one explicit two-world universally accessible frame, invariant-filtered NE holds but unrestricted Scott NE fails. |
| [`SCOTT-MODAL-COLLAPSE`](../corpus/results/SCOTT-MODAL-COLLAPSE.json) | Derived conditionally | From the same Scott axiom set used for T3, every proposition implies its necessity in the embedding. This is not a theory-free property of God. |
| [`GOEDEL-1970-INCONSISTENT`](../corpus/results/GOEDEL-1970-INCONSISTENT.json) | Inconsistent conditional axiom bundle | The specified 1970 Ax2a, Ax3 and Ax4 cannot hold at any world in that **different** embedding. Scott's essence and NE are not the 1970 definitions. |
| Positivity of Scott's NE, `P(NE)` | Open substantive commitment | A5 is independent of the preceding axioms. Neither the independence model nor a world-isolation characterization proves that the axiom is false or rationally unjustifiable. |
| Metaphysical admissibility of properties | Open | Neither unrestricted HOL comprehension nor world-invariance has been justified as the correct domain of genuine essences. Other defensible restrictions and actualist existence predicates remain to be tested. |

## What the new comparison establishes

The variant `FilteredEssence` restricts its comparison properties `Ψ`; `FilteredNecessaryExistence` restricts its candidate essences `Φ` using the **same** fixed admissibility predicate. This is a stipulated control, not an AFP source reading. The unrestricted agreement theorem guards against accidentally changing more than the property domain.

The two boundary cases matter: admitting every intensional property makes NE sensitive to the identity of accessible worlds, while admitting only world-invariant properties makes the filtered test automatically pass. **Neither extreme supplies a metaphysical account of why something exists or why necessary existence is positive.** The finite model only separates formal definitions; it does not rank complete worldviews or discharge a root premise.

## Next obligations

1. Formulate a principled middle admissibility condition and a nontrivial finite model. Test the filter's treatment of haecceities, world-indexed properties, essence possession, and any explicit existence predicate; do not select a condition because it proves a desired theology.
2. Compare source-grounded Anderson and Fitting alternatives under their *own* quantifier and positivity semantics, keeping Scott and Gödel 1970 separate.
3. Independently defend or challenge `P(NE)` and clarify how formal `NE` could connect to metaphysical necessity, actuality and grounding. These are still epistemic-frontier questions, not completed Lean theorems.
