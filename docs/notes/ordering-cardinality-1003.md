# Ordering cardinality and the infinite-regress question (#1003)

The owner's argument has a correct mathematical component: a countably infinite
**labeled** roster has continuum-many distinct arrangements, more than its
members. This does not establish that an infinite causal regress is impossible.
The formal comparison exposes the additional explanatory demand and preserves
three strong objections, rather than attributing that demand to cardinal theory.

## What is counted

`Arrangement := Equiv.Perm Nat` enumerates one fixed labeled roster exactly
once. `earlier e x y` compares the positions of the same labels x and y.
The result `ORDERING-CARDINALITY` combines Mathlib's
`Cardinal.mk_perm_eq_two_power`, `Cardinal.mk_nat` and `Cardinal.cantor`:

- the enumerations have cardinality `2 ^ aleph0`, strictly above `aleph0`;
- distinct enumerations induce distinct strict order relations;
- the range of these relations itself has cardinality `2 ^ aleph0`.

For the injectivity proof, an equality of transported orders makes each
comparison map between the two enumerations strictly increasing on Nat. Each
map is at least the identity. Since the maps are inverses, each is exactly the
identity, and the enumerations agree.

These are orders of type omega on **fixed labels**, or omega-star on reversing
the orientation. Forgetting the labels leaves the same isomorphism type in every
case. No counting of unlabeled order types, causal capacities, physically
realizable histories or metaphysically accessible worlds is asserted. Nor is
there a defined cardinal measure of an "unexplained remainder": more alternatives
are not by themselves more unexplainedness.

The enumeration index is an ordinal position, not physical time. `next e x`
is one step farther upstream. Every label has an upstream predecessor;
`e 0` is the selected terminal, not a source. The relation
`y = next e x` is not well-founded. This is a mathematical interpretation;
it is not an independently justified interpretation of actual causation.

## R1: the links already fix the order

`ORDERING-REGRESS-RIVAL-CONTROLS` proves `chainData` injective. This data is
exactly the endpoint and the entire immediate-link function. A finite induction
shows that another enumeration with the same endpoint and links has the same
label at every position. Permuting labels therefore changes the whole labeled
chain; it does not vary an extra order while retaining identical complete links.

The strongest reply is that no further arrangement fact needs a separate reason
once the links themselves have been explained. The remaining question is why
these links or this whole chain obtain. The result does not answer that question,
and the mere fact that the complete table determines the order gives no warrant
for the table's actuality or its explanatory sufficiency. This is the same
informational-versus-adequacy boundary as `HISTORY-SELECTION-CERTIFICATE`, with
its `EvidenceOnly` definition reused literally; ordering facts are not renamed
presence histories.

## R2: cardinal abundance does not discriminate regress

The same controls exhibit `2 ^ aleph0` binary vectors `Nat → Bool`, alongside
a well-founded **empty dependency relation on Unit**. This is an abstract model
of continuum-many state assignments with no regress in that dependency graph.
It refutes the mathematical inference from this number of alternatives alone
to a non-well-founded dependency relation. It neither establishes that a real
single bearer has these states nor judges such a bearer adequately explained.

Conversely, each enumerated backward chain has a predecessor everywhere and
fails well-foundedness. Both structures are compatible with the cardinal
calculation. Thus alternative count alone cannot establish the existing
`STMT-NO-INFINITE-REGRESS-OF-CAUSES-OF-A-PERFECTION`. That target also ranges over
all respects and excludes cycles of distinct causes, not just the single
countably infinite linear pattern studied here.

The stronger philosophical objection says that even a finite chain or one
contingent state's value may admit many alternatives. A universal demand to
explain which obtains is a PSR-type commitment applying symmetrically to finite,
infinite, theistic and impersonal accounts. The formal control supplies the
mathematical counterexample; a claim about the actual range of contingent facts
would need independent metaphysical vocabulary and warrant.

## R3: verification is not grounding

General reconstruction is conditional on a seed and an applicable rule. It
uses induction rather than an infinity of separate checks. To avoid merely
moving all verification into that rule hypothesis,
`ORDERING-FINITE-RULE-VERIFICATION` also provides a **closed** example: the
finite recursive program starting at zero and taking successor generates n at
position n, and the identity enumeration's upstream rule is `n + 1`, for every
n. Its proof assumes no collection of test results for all n.

This defeats a general claim that infinitely many mathematical cases require
infinitely many separate verifications. It does not prove that any proposed
physical or metaphysical law is actual. The defensible remaining question is
what grounds a rule's holding in reality, not how a finite mathematical proof
can quantify over infinitely many cases. Actual applicability needs a bridge;
it is not a failed induction obligation.

## The open explanatory bridge and its rival

`STMT-COMPLETE-CHAIN-EXPLANATION-SELECTS-ARRANGEMENT` records the **local** demand
for the designated arrangement a: every candidate accepted by the supplied
adequacy judgment must be true there and exclude every different arrangement.
`STMT-COMPLETE-CHAIN-EXPLANATION-ALLOWS-UNSELECTED` records the rival that some
accepted candidate fails this entailing test. Both are openly stipulated
framework options; no historical author is credited with either.

The strongest rival may regard the local links as exhausting the structural
question, accept an intrinsic stopping point, or accept a probabilistic or
noncontrastive explanation that leaves alternatives. It does not declare every
uninformative sentence an explanation. The supplied adequacy judgment is an
explicit open parameter, not an established flag; no causal, transitive,
asymmetric or well-founded properties are silently imposed on it. Choosing
which candidates deserve that judgment is an unencoded philosophical assessment.

On the same arrangement arena, the controls prove that **constant** evidence
cannot support an evidence-only entailing selector: a swapped-label rival shares
all that information. By contrast, the full endpoint/link equality vector does
support such a selector at every designated arrangement. These are different
information supplies to the same test. The complete vector may simply copy the
target. Neither that success nor the constant-vector failure establishes
independent explanatory relevance, causal production, actual applicability,
agent access, or the truth of either adequacy commitment.

Even granting the local bridge would not yet prove that infinite regress is
impossible: one must show that an infinite chain could have no accepted
complete explanation. Counting its alternatives does not show this. No such
inference or refutation is registered.

## Premises, sources and verification boundary

The three certificates are closed mathematical/informational results under
Mathlib's allowed `propext`, `Classical.choice`, `Quot.sound` axiom policy.
The explanatory bridge and its rival are open statements, not premises secretly
used by those proofs. No new source claim is introduced. Leibniz's copied-books
argument is a source lead in the issue, not a passage read or attributed here.

The existing no-infinite-perfection-cause-regress premise remains supported and
open. No argument deriving it is added. Intended root-frontier change: none;
the PR reports the computed `corpus.py frontier-diff` output rather than a new
hand-counted route estimate. Verified attempts, rejected inferences and remaining
burdens are retained in `ATTEMPT-ORDERING-CARDINALITY-1003`.
