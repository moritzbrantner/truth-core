# Support for priority, independence and excluded middle

Research date: 2026-11-13. Evidence baseline:
`03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`.

This investigates four of the nine common terminal inputs identified in the
[God-existence calculation](god-existence-support-formula.md). The companion
[nine-premise assessment](nine-premise-support-investigation.md) connects the
findings. Existing statement meanings and proof records are unchanged.

## Exact targets and meanings

Write `D(x,y)` for the existing `DependsForBeing x y`, `B(x,y)` for
`CanBeWithout x y`, and `P(y,x)` for `PriorSimply y x`.

| Target | Existing formula |
| --- | --- |
| `STMT-PRIORITY-REQUIRES-NONMUTUAL-DEPENDENCE` (`47aff057-35ef-5418-930b-fef72e1104d2`) | `∀ y x, P(y,x) → D(x,y) ∧ ¬D(y,x)` |
| `STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT` (`8ab3d114-d6e2-5f6d-805b-ae901f56d39b`) | `∀ y x, ¬D(y,x) → B(y,x)` |
| `STMT-PRIORITY-BY-BEING-WITHOUT` (`97fa3a0b-eb23-5fb1-9741-c1f09fb72206`) | `∀ y x, B(y,x) → ¬B(x,y) → P(y,x)` |
| `STMT-EXCLUDED-MIDDLE` (`ee4ab504-c8fe-59bc-bc96-7cbeefed6410`) | `∀ p : Prop, p ∨ ¬p` |

The meanings matter. `D` is the stipulated counterfactual relation in
[depends-for-being.json](../../corpus/definitions/depends-for-being.json),
including counterfactuals with impossible antecedents. It is not defined as
necessary co-existence. `B` is real possibility of one being without the other.
`P` is the primitive non-temporal relation constrained by the act/potency
readings, not definitionally either `D` or `B`. See
[simple-priority.json](../../corpus/definitions/simple-priority.json) and
[can-be-without.json](../../corpus/definitions/can-be-without.json).

The arguments below are explicit research reconstructions. They are not newly
registered or Comparator-certified implications. Existing theorem references
are reused at their recorded scope; no new theorem verification is claimed.
Direct consideration of each proposition remains available alongside every
conditional argument proposed here.

## 1. Priority requires nonmutual dependence

### Positive support and an exact source bridge

Aquinas's *In V Metaphysicorum*, lecture 13, nn. 15–18, connects priority in
being with one-way dependence. The whole Latin lecture was materialized and
read. The existing source claims already preserve the relevant limits:

- `ab5ec574-cd80-5c16-b391-328245425d21`, n. 15, supports the criterion for
  **natural priority in being**.
- `95f41960-baf4-58ad-ba7f-b11b2f439f7c`, n. 18, concerns pairs **already
  ordered as prior and posterior**, retaining the qualification that the prior
  can be without the posterior in some way.

The primary text is available in
[Latin and English](https://www.logicmuseum.com/wiki/Authors/Thomas_Aquinas/metaphysics/liber5/lect13).
It offers substantive historical and conceptual support for a directional
explanatory reading. It does not by itself identify that reading with the
repository's counterfactual `D` or its act/potency `P`.

One precise proposed support package is:

1. On the selected domain, every `P(y,x)` is priority in the source's
   existential/explanatory sense.
2. That priority carries dependence of the posterior on the prior and absence
   of the reverse dependence.
3. Those two dependence judgments faithfully transport to the existing `D`,
   including the intended treatment of impossible antecedents.

This package supports the exact target. Its contribution is to isolate the
historically supported premise from the two interpretation bridges, rather
than disguise either bridge as a quotation. The reason to favor the explanatory
reading is that priority then explains why a posterior is available or
actualized. Temporal precedence or comparative excellence alone supplies no
such explanation.

### A second support route through strict grounding

The [causal-dependence investigation](causal-dependence-support-investigation.md)
identifies an existing strict-grounding asymmetry theorem. A candidate use here
would require:

- a mapping of `P(y,x)` to strict grounding of the existence of `x` by the
  existence of `y`;
- grounding-to-`D` transport in the forward direction;
- transport of a hypothetical reverse `D(y,x)` to the reverse strict ground;
- the grounding theory's consistency assumptions.

The existing acyclicity result would then exclude the reverse dependence.
The last transport must be present: asymmetry of grounding alone does not
exclude an unrelated counterfactual dependence. This route adds explanatory
structure and a reusable theorem, while leaving its applicability explicit.

### What the consumers actually need

The four registered direct consumers were inspected, including their proof
bodies:

| Existing consumer | Use of the target |
| --- | --- |
| `Round5Worklist.simplyPriorCausesBeing` | Only `P(y,x) → D(x,y)`; it then uses the separate dependence-to-cause premise. |
| `Round2Grounding.simplyPriorGroundViaDependence` | Only the same forward half, together with actual-concrete and grounding bridges. |
| `CausalMapsBatch1.nothingPriorToItself` | Applies both halves on the diagonal to derive `¬P(x,x)`. |
| `Round2Grounding.asymmetricViaPriority` | Applies both halves to two opposed priority edges. |

Thus a future sibling of each of the first two arguments can use only the
forward half. This is a concrete reduction in the claim requiring support,
not a proof of that half. Existing frozen Challenges are not changed.
Deriving priority's irreflexivity from this target and then using that result
to justify this same target would add no warrant by itself.

**Provisional assessment:** the directional explanatory principle has good
conceptual and textual support. The exact global statement over the existing
primitive relations remains conditional on interpretation transport. Further
progress should certify the two weaker consumer interfaces and test the
grounding transport on the actual existential domain, rather than introduce
another opaque priority label.

## 2. Independence allows being without

### The strongest positive route: realizable separation

There is a constructive mechanism supporting independence-to-separation on
appropriately modular systems. It needs more than the bare absence of a
dependence edge. Here is an explicit mathematical reconstruction.

Let `R(a,b)` mean that retaining `a` requires retaining `b`; take `R` to be
reflexive and transitive, incorporating indirect requirements. Let `N` be the
beings required by the background. For a proposed retained being `y`, form

```text
C(y,N) = { z | R(y,z) or there is n in N with R(n,z) }.
```

This set contains `y` and `N`, and is closed under the requirements `R`:
transitivity sends every requirement of a member back into the same set.
Suppose:

1. `¬R(y,x)`;
2. no member of `N` requires `x`;
3. a state with exactly the retained beings `C(y,N)` is genuinely admissible,
   with the intended identities, laws and existential conditions preserved.

Then that state retains `y` and omits `x`, supplying the witness for `B(y,x)`.
No well-foundedness or finite-domain premise is required in this set-theoretic
argument. The third premise is the substantive realization bridge; declaring
all closed subsets possible would be a stronger framework assumption.

To use this for the existing `D`, one must additionally justify that
`¬D(y,x)` licenses the absence of an `R`-requirement for the selected pair.
Removing a direct causal edge is insufficient when an indirect requirement
remains. Necessary background beings must stay in `N`. The mechanism is useful
because it makes the support task specific: exhibit a way to preserve the
actual grounds and identity of `y` while omitting `x`, or justify closure-state
realizability in the selected domain.

This is positive conditional support, not an assertion that every metaphysical
domain is modular. Empirical success at separating particular components would
support those instances and the relevant modeling bridge; it would not
establish universal metaphysical recombination.

### A weaker premise sufficient for the existing argument

The only registered direct consumer is
`TruthCore.Results.Causality.Round2PerfectionPrimacy.nonmutualDependenceSuffices`,
result `47957c28-218a-58e4-94e4-5220a0c45795`. Its proof uses independence only
when it already has the other direction of dependence. Replace the universal
allowance in a **new sibling argument** by the proposed local input

```text
∀ y x, D(x,y) → ¬D(y,x) → B(y,x).
```

Together with the unchanged dependence-excludes-being-without and
priority-by-being-without premises, this still supplies the same
`NonmutualDependenceSufficesForPriority` conclusion: derive `B(y,x)` from the
local input, derive `¬B(x,y)` from `D(x,y)`, and apply the priority criterion.
This avoids requiring separability for unrelated pairs. It is not yet a
registered replacement or a claim that the weaker premise is true.

Aquinas n. 18 cannot by itself supply this local input: its argument already
starts with a prior/posterior pair, whereas this consumer is trying to establish
priority. Using that sentence with no separate bridge would assume the target
relation too early.

### Exact constraints, not hypothetical objections

For an explicit possible-world interpretation, put

```text
B(y,x) = ∃ w, admissible(w) ∧ ExistsAt(w,y) ∧ ¬ExistsAt(w,x).
```

If `x` exists in every admissible world, then `B(y,x)` is false. Therefore the
global allowance would imply `¬¬D(y,x)` for every `y`, and classical logic
turns this into `D(y,x)`. This is an exact consequence of the allowance. It
does not establish that an actual being is independent of a necessary being,
or refute the allowance merely by imagining such a being.

There is also a useful joint-premise diagnostic. The two universal premises

```text
D(y,x) → ¬B(y,x)
¬D(y,x) → B(y,x)
```

imply, with excluded middle, `D(y,x) ↔ ¬B(y,x)`. Hence the bundle identifies
counterfactual dependence with modal inseparability, although the definition
records deliberately distinguish them. Adding the distinct-being
nonmutual-dependence premise then excludes distinct beings with mutual modal
inseparability. These are conditions the joint interpretation must satisfy,
not evidence by themselves against a metaphysical premise.

**Provisional assessment:** favor the explicit separation mechanism and the
consumer-local version as support projects. The unrestricted allowance is not
currently supported by the cited source alone. Keep the original proposition
as a direct option, and also keep direct consideration of
`STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY`: explanatory priority can be
assessed without taking a modal-separation detour.

**Reopening conditions:** an actual-domain separation construction with its
background retained; an independently warranted identification of `D` with
modal prerequisite; or a justified direct explanatory-priority bridge. Showing
only that `x` is contingent does not supply a state in which `y` survives its
absence.

## 3. Priority by being without

The existing n. 15 claim gives substantial support for **one criterion of
natural priority**. A proposed exact route to the target is therefore:

```text
one-way being-without ⇒ natural priority in being
natural priority in being ⇒ the selected simple priority P.
```

The first arrow has an existing source statement,
`fa759767-0de7-5b9b-a3bd-3106d6e1dedc`. The second is an explicit
interpretation bridge still to be defended for the act/potency use of `P`.
Its attraction is that a nonreciprocal existential prerequisite identifies a
real order of presupposition, rather than merely an earlier date. To carry
explanatory force, however, the prerequisite must concern the relevant
actuality or existence, not an incidental necessary co-presence.

[Aristotle, *Categories* 12](https://classics.mit.edu/Aristotle/categories.3.3.html)
distinguishes priority by nonreciprocal implication from a further causal sense
that can hold with reciprocal implication. His example is the relation between
a person's being and the truth of the corresponding statement: the former
explains the latter. This supports retaining an explanatory route alongside
the separability criterion. It is not an instance involving two concrete
existential bearers, so it does not by itself refute the exact `P`/`D` thesis.

**Provisional assessment:** retain this as a well-motivated sufficient
criterion for the natural-priority reading, with the simple-priority transport
explicitly open. Do not turn the sufficient criterion into an exhaustive
definition of every explanatory priority. Test the transport against actual
act/potency cases and preserve the same respect, domain and modality.

## 4. Excluded middle

### What supports accepting it

The exact target concerns whether propositions hold, not whether we possess
proofs or assert them. For precise ontic claims, treating a proposition and its
negation as exhaustive is a credible basic rational commitment. Distinguishing
unknown truth from lack of truth is a reason for retaining this commitment in
an inquiry about reality. This is a prima facie and semantic defense, not a
deduction of global excluded middle from weaker logic.

Aristotle's *Metaphysics* IV.7, 1011b23–29 and 1012a17–24, supplies a direct
statement and a defense from determinate signification and truth. The
materialized Greek chapter was read with the
[Ross translation](https://classics.mit.edu/Aristotle/metaphysics.4.iv.html).
The source does not provide a neutral demonstration accepted by every theory
of meaning.

Three existing logical results sharpen this defense:

| Existing result | Contribution and limit |
| --- | --- |
| `3be6adf4-216f-53a0-b69b-084ac5fc7e48`, `ExcludedMiddleIrrefutable.excludedMiddleIrrefutable` | Constructively establishes `∀p, ¬¬(p ∨ ¬p)`. A denial of an individual instance defeats itself. |
| `d36bd424-9fe4-5a67-a109-7d0c5c419e06`, `ExcludedMiddleNotDeniable.noExcludedMiddleInstanceDeniable` | Excludes `∃p, ¬(p ∨ ¬p)`. It does not eliminate withholding or prove the universal target. |
| `e2d8d9a4-ecab-5d32-8c57-4109df41dbb6`, `ExcludedMiddleIffDne.excludedMiddleIffDoubleNegationElimination` | Makes double-negation elimination an exact alternative commitment. It is an equivalent route, not independent corroboration. |

The existing
`ThoughtBivalenceIffExcludedMiddle.thoughtBivalenceIffExcludedMiddle`
also shows why one must not advertise universal thought-bivalence as an
independent proof. Under its explicit semantic and coverage premises,
thought-bivalence is equivalent to excluded middle. This is useful analysis of
the support package, not a reason to discard either prima facie commitment.

Heyting's [*Disputation*](https://math.dartmouth.edu/~matc/Readers/HowManyAngels/Disputation/Disputation.html),
opening exchange on the two prime-number definitions, explains the substantive
constructive alternative: mathematical existence and assertion are tied to
constructions, and the availability of a decision matters. The distinction
between this task and ontic truth is explicit in the dialogue. The disagreement
is not answered by confusing a missing proof with an assertion of
`¬(p ∨ ¬p)`. No new attribution record is created from this corroborating
reading. The existing
[assertion-boundary analysis](excluded-middle-assertion-boundary.md) remains
authoritative for the corpus's logical and assertion targets.

**Provisional assessment:** retain excluded middle as a credible basic
commitment for the present exact ontic inquiry, supported by its semantic role
and constructive resistance to instance-denial. This does not derive the
unrestricted principle or defeat the constructive alternative under its own
meaning and proof policy. No new floor marking is introduced; the legacy
computed `self_evident` status is not fresh warrant.

### A concrete additional support route: local decisions

A proof or refutation of a particular `p` constructively gives `p ∨ ¬p`.
Accordingly, supplied decision procedures can justify the classical choices
actually used by a theorem without requiring a decision procedure for all
propositions. This is a genuine alternative support option when those
procedures or local disjunctions are available.

The recorded 39-input example has four registered rules with an explicit
excluded-middle input. Inspection reveals these particular demands:

| Consumer inspected | Actual decision demand visible in the proof |
| --- | --- |
| `Round3FourthWay.maximumInGenusFromGreatestEveryGenus` | Degree-order comparisons `deg r z ≤ deg r m`. |
| `Round3FourthWay.gradesAtBeingFromNoInfiniteAscent` | Whether a given bearer has a strictly greater bearer, `∃y, MoreIn esse y x`. |
| `MaximalGroundingAsymmetry.WholeRoster.wholeRoster` and its `actualRootMaximum` helper | The maximum/unbounded fork and equality of candidate beings. |
| `GradesAtBeingRoutes.existenceOnlyGodExistsAtBeing` and its imported root/maximality helpers | Existence of a source/root, maximum extraction and equality of candidate beings. |

These are families of propositions, not a claim that the graph supplies a
finite decision algorithm. Decidable order or equality is not decidable
unbounded existential search. A local-logic sibling must expose every required
decision and audit imported helpers before it can replace global EM. No such
registered replacement is claimed here. Concrete next work is to use local
order decisions where available, while retaining explicitly the harder
existence decisions or the global primitive.

## Structural checks and publication boundary

The new modal and separation analyses were also tested by exhaustive Python
enumeration. These are finite checks of the declared surrogate, not Lean
certificates or empirical evidence:

- all 32 Boolean assignments to the local allowance calculation: 14 satisfy
  its retained background and none fails the conclusion;
- 16 two-world/two-being presence profiles, each paired with all 16 dependence
  relations: the two global bridge conditions admit exactly the dual relation
  in each profile;
- every three-element preorder (29), every background subset (8), and every
  ordered pair: 2,088 cases, including 348 separating cases; the constructed
  closure contains the retained being and required background, is closed, and
  omits exactly the excluded requirements.

The general set argument is given above; finite enumeration does not establish
its unbounded counterpart. Independent semantic review covers the proposed
reasoning and interpretation limits. Repository corpus checks validate the
attempt references. No statement, result, argument, floor, or source-claim
status is changed by this investigation.
