# Van Inwagen's aggregate argument: sources and the derivative-facts reply (#365)

Lean: `DerivativeReply` in `TruthCore.Explanation.BCCFDerivative`, proved as
`derivativeReply` in `TruthCore.Results.Explanation.BCCFDerivative.Solution` with no
axioms. It establishes conditional consequences and satisfiable encodings: no PSR, no
reply, no premise on a root route and no model's metaphysical possibility.

## Sourced readings

Each row states what the cited text says. "Member" is my mapping to `CollapseCore`
(#755), not the author's vocabulary, and the mapping is an interpretive judgment.

| Reading | Witness | Member affected |
| --- | --- | --- |
| Pruss formulates the argument with premises (11)-(15), credits it to van Inwagen (1983, pp.202-204), calls it plainly valid (read; no claim yet, because of the PR file limit) | `PRUSS-LCA-2-3-2` | The form the members model. His (11) is not a member: `Necessitating` is the stronger premise (27) that he says motivates it |
| Pruss says we should not accept (11), attacks (24), and says its contraposition (27), that what explains entails, is falsified by just about every modern scientific non-conceptual explanation he knows (`PRUSS-LCA-EXPLANATION-NEED-NOT-ENTAIL`) | `PRUSS-LCA-2-3-2` | `Necessitating` denied |
| Della Rocca tends to think the PSR entails necessitarianism, and expects a clear-headed proponent to embrace it (`DELLA-ROCCA-PSR-ENTAILS-NECESSITARIANISM`) | `DELLA-ROCCA-PSR-PP1-10` | `Contingent` is the member a proponent gives up; this does not state that he asserts necessitarianism |
| Dasgupta says that for ground the inference to each conjunct is invalid (`DASGUPTA-MR-GROUND-CONJUNCTS`) | `DASGUPTA-MR-1-6` | `Distribution` denied, for ground only. The same section argues by another route to necessitarianism |

Further text read and not made a claim: Pruss §2.3.2.2-3 gives conditions on a
libertarian's position, namely denying (27) or holding a free choice nearly
self-explanatory, which he calls a counterexample to (12) when the agent necessarily
exists freely and omnisciently. §4.1.1.3 (`PRUSS-LCA-4-1-1-3`) records a set-theoretic
worry about forming the aggregate and says that if nothing like it can be formed, the
objection fails. Koons (2001) and Oppy (1999) are in a separate intake change.

Not read, so not attributed: van Inwagen (1983, 2002), Bennett (1984), Pruss (2006),
Gale and Pruss. A candidate waiting for those witnesses is in the companion intake
change. Dasgupta's footnote 29 says his presentation is based on Della Rocca's.

Senses: `DEF-PRUSS-EXPLANATION-ENTAILMENT`, `DEF-DELLA-ROCCA-PSR`, `DEF-DASGUPTA-GROUND`.
`DISAMB-BCCF-DERIVATIVE-REPLY` says where each mapping crosses from an author's sense to
an analyst's. Dasgupta (§3, p.385) calls a fact derivative when it is apt for a ground
and has one, beside brute and autonomous facts. That is his taxonomy, not `D`, and he
does not state the owner's reply.

## The relation

`G w Xs f` reads: at `w`, the facts `Xs` are together admitted as a reason why `f`
obtains.

- **Ordinary language.** "The meeting happened because Ann came and Bob came", where
  neither arrival alone is the answer.
- **Examples and counterexamples.** A conjunction and its conjuncts together. A
  counterexample to treating `G` as distributing: "Ann came and Bob came" answers why
  both came and is not thereby an answer to why Ann came.
- **Not the same as.** Single reasons (`Arena.explains`, which embed through
  `ofSingle`), ground in Dasgupta's sense (the relation here is general), causation
  (`Ontic.Causes`), and modal sufficiency (`PNecessitating`, a separate hypothesis).
- **Structural properties.** None is assumed. Well-foundedness, closure, distribution,
  and contrast are named hypotheses because they are in question.
- **Generalization.** None. Each condition is under test.
- **Competing accounts.** Necessitating and nonnecessitating reasons, and class and
  plural readings of the reply, all have a certificate row below. Probabilistic and
  weaker contrastive accounts have none.

`D` is a parameter whose only commitment is `ClosedUnderReasons`: a fact in `D` has no
contingent reason outside `D`. The owner's reply is formalized, not sourced, and has two
readings (`DISAMB-BCCF-DERIVATIVE-REPLY`).

## What the test shows

**Premise denied.** The class reading leaves the aggregate without a reason, so it
denies coverage at the aggregate (`scopeOnly`). The plural reading gives the aggregate
a reason, so it denies distribution over it (`bruteMembers`, `loopMembers`, `chain`).

**(a) Does a totality of direct facts bring the argument back?** Conjunct 2: yes, with
no assumption that the totality is direct, if it has a reason that distributes over it,
`D` is closed and contains a contingent truth, and the other listed conditions hold. So calling the totality derivative does not itself block the
argument. The work is done by denying the reason or the distribution.

**(b) Is "explained by its grounds" an explanation in the PSR's sense, or a scope
restriction?** Each reading pays. On the class reading the aggregate is brute
(`scopeOnly`). On the plural reading the aggregate has a reason, and conjunct 3 needs
no aggregate and no distribution: on a closed class, coverage, factive necessitating
reasons and well-foundedness exclude contingency. So the plural reading keeps
contingency in `D` only with one of the deletions below, or by rejecting bivalence. In
`bruteMembers`, with `D` the two members, the only facts lacking a reason are in `D`.

| Deleted from conjunct 3 | Model | What survives |
| --- | --- | --- |
| Coverage of `D` | `bruteMembers` | Members with no reason; aggregate has a reason |
| Well-foundedness | `loopMembers` | A reason for every contingent truth, members in a circle |
| Well-foundedness | `chain` | A reason for every contingent truth, an endless chain, no fact below itself |
| `PNecessitating` | `ground true`, through `ofSingle` | A reason true at every world for a contingent fact; distribution kept |
| Closure | `outsideReason` on `pairOutside` | A direct fact with a contingent reason outside the class |
| Factivity | `outsideReason` on `pairToken` | A reason true nowhere |
| Contingency | `noReasons` on `pairNecessary` | Nothing contingent |

Bivalence has no deletion model; every model meets it. The table is not a claim of minimum cardinality.

**(c) Contrast.** Conjunct 4: read as "at every accessible world where the target fails,
some reason fails", contrast does the work of necessitation, and with bivalence it gives
necessitation (conjunct 5). So on that reading the reply is not helped by a contrastive
reason. `ground true` fails this condition. Weaker contrast, against some selected
rival, was not tested.

Standard rivals: "explanation need not entail" is the `ground true` row; "there is no
such aggregate" is `cofinite` in `CollapseCore`; brute contingency is `bruteTerminus`
there. The signature cannot separate a necessary personal ground from an impersonal one
(#755), so none of this favors a worldview.

## Open

- The #364 Part D Cantorian obstacle is not formalized here; Pruss §4.1.1.3 is pinned for it.
- Weaker contrast, and `D` in the sense of #348's strict ground, are not tested.
- Premise (11) has no separate Lean form: `Necessitating` gives it through #755's
  lemma that a true necessitating reason for a contingent fact is contingent.
- No text read states the owner's reply, so its fit with what the owner means is a question
  for the owner, not settled by these records.
