# Can Grim Reapers prove the *per se* causal-regress premise?

**Target:** `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`, the still-open
Second Way claim interpreted as well-foundedness of `CausesAsCaused`. The current
corpus has a sourced reading but no independent proof of this claim. The result
`AQUINAS-ST-I-Q2-A3-SECUNDA-VIA` uses it as a premise; it does **not** establish
it. Likewise, an infinite chain of temporal causes *per accidens* is not the
same claim as an essentially ordered chain exercising power *per se*.

## 1. The no-first-deadline Grim Reaper test

Consider Reapers with deadlines indexed by `Nat`; a higher index signifies an
earlier deadline. There is no earliest deadline. Give each Reaper the rule:

> Reaper `n` acts **if and only if** no Reaper with a higher index acts.

Formally, `acts n ↔ ∀ m > n, ¬ acts m`.

The axiom-free Lean result
`GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` derives a contradiction:

1. If some Reaper `n` acts, no higher-index Reaper acts.
2. In particular, none higher than `n + 1` acts. The rule then **requires**
   `n + 1` to act, contradicting (1).
3. So no Reaper acts. The rule for index `0` then requires Reaper `0` to act,
   again contradicting the supposition.

This is an inconsistency of **that combined schedule and rule**, not of an
infinite ordered set alone. The companion model
`FINITE-GRIM-REAPER-SCHEDULE-CONSISTENT` verifies that three Reapers with the
same rule are consistent: the maximum-index (earliest-deadline) Reaper acts.

The law already captures the strong assumption that there is an action at a
deadline exactly when none has occurred earlier. A physical story adds more
assumptions: a victim initially alive, each Reaper capable of acting, no
unrelated death or resurrection invalidating that equivalence, and the
specified deadlines and counterfactuals being jointly realizable. Dropping or
weakening these assumptions may dissolve the contradiction.

## 2. Why this does not yet establish the target

The per se premise in Aquinas, *Summa theologiae* I q.2 a.3, concerns the
simultaneous dependence of an intermediate efficient cause on another. A
Grim Reaper sequence, by contrast, is a supertask-style arrangement of
events ordered **in time**, with a specialized inhibition rule. Neither the
temporal order nor its action rule follows from the definition of `CausesAsCaused`.

`INFINITE-LOCAL-TRANSMISSION-MODEL` makes the underdetermination explicit:

- There is a predecessor relation `R (n + 1) n` with no first member.
- All nodes are currently active, so each satisfies the **local** condition
  `active n ↔ active (n + 1)`.
- Nevertheless `R` is not well-founded (`¬ Acc R 0`).

This is a consistent mathematical model. It is **not** a demonstrated possible
world containing genuinely derivative efficient causes. In particular, a
defender may insist that "causing only as caused" imposes more than matching
activity: a power must actually be *grounded*, not just locally correlated.
But that stronger meaning must be specified and independently defended.

The exact missing step is a **transfer principle** of roughly this form:

> If a genuinely *per se* cause-chain had no first, its powers and dependencies
> could be arranged into a jointly possible Reaper-type configuration with the
> stated action rule.

This is related to a causal-network *patchwork* or recombination principle.
It is not pure logic. Merely assuming "no first entails no effect" as the
transfer principle would restate the desired conclusion and beg the question.
Formalizing a conditional proof from an explicitly assumed transfer principle
is straightforward, but would close no frontier premise until that principle
itself is justified. No such axiom is included in these verified results.

## 3. The deeper issue: which notion of grounding?

An equation at every link, `power(n) = power(n + 1)`, for binary power has two
uniform solutions (every link powerless or every link powered). These are
**genuine, explicitly defined mathematical objects**, but the *equations*
alone do not specify which one is intended.

The stronger theorem `ESSENTIAL-POWER-UNDERDETERMINED` tests whether making the
link's *essential* nature more precise fixes the problem. Its rule says a node
is active **exactly when an immediately upstream cause is active**. It
establishes all of the following without axioms:

1. The whole infinite chain can be active, while a different assignment
   satisfying the same equations has no active members.
2. For **any** chosen link, we can cut it and give a consistent assignment
   that preserves activity above the cut but leaves the cut node and **every
   downstream node inactive**. This models the counterfactual indispensability
   of its immediate cause to the downstream effects.
3. The uncut chain is still not well-founded.

This answers an objection to the earlier `LocalTransmission` countermodel:
even explicitly modeling the removal of instrumental support does not *by
itself* select a unique global source of power. The intervention result is an
**existence of an admissible response**, not proof that real causal powers
must obey exactly these equations or that every intervention has that response.

The contrasting theorem `FINITE-GROUNDING-HAS-SOURCE` takes a different, more
explanatory reading. A node's power is **inductively grounded** when either it
has intrinsic power, or it receives power along one actual link from another
node whose power is already inductively grounded. Lean constructs a finite
path from every such active node to an intrinsic source. If no source exists,
no act in this *inductive* semantics can be established.

Both mathematical approaches are internally coherent. The choice of
inductive (rather than coinductive, greatest-fixed-point or global) grounding
semantics is **a philosophical premise**, not a theorem about natural numbers
or about the Reapers. It cannot simply be hidden inside the meaning of
`CausesAsCaused` to close the Second Way frontier.

This addresses the worry about endlessly deferred *mathematical definitions*:
mathematicians do insist on unambiguous semantics, but infinity by itself is
not a flaw. Implicit or recursive definitions may work through existence and
uniqueness, or through an explicitly chosen least or greatest fixed point.
Tarski's original [lattice-theoretical fixed-point
theorem](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf)
shows why a monotone self-reference can have a collection of fixed points
with least and greatest members. Existence need not imply uniqueness. What
our successor-chain equations lack is **a justified selection of the intended
solution**. What a metaphysical causal explanation might additionally lack
is an *independent actualizer*, but that claim requires separate argument.

The result `LOCAL-OBSERVATION-SELECTS-SOLUTION` sharpens this qualification:
**once activity or inactivity at node zero is supplied as a fact**, induction
on the index uniquely fixes the activity of every other link in the local
successor chain. So *non-uniqueness without a boundary condition* is not an
argument that the chain is mathematically impossible; one observed effect can
select a solution. **What explains that effect** is a different question.

### Fixed-point reuse audit for #310 (2026-10-28)

At `49b4589aa6744c91a6bc9adec13215d0e7245c9d`, the proposed
least-versus-greatest activation test is already substantially covered:

- `TruthCore.Logic.Regress.Graph.transmission` takes the original-power
  predicate `O` as independent data and sends `S` to
  `{x | O x ∨ ∃ y, R y x ∧ y ∈ S}`. Its monotonicity is proved.
  `Graph.grounded_eq_lfp` identifies its least fixed point with the existing
  `FinitelyGroundedPower R O`, without assuming well-foundedness of `R`.
- `TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource`
  extracts `∃ s, FiniteCausalPath R x s ∧ O s` from that inductive membership.
  Conversely the constructors `FiniteCausalPath.same/link` and
  `FinitelyGroundedPower.intrinsic/borrowed` give the reverse construction by
  induction on the path. This reverse construction is an inspected structural
  consequence, not a newly registered or separately certified theorem here.
- `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage`, through
  `RegressDomains.CrossDomainBoundary`, already certifies the same successor
  graph with every node active, no graph source, `0` in the greatest fixed
  point and `0` outside the least fixed point for `O = False`.
  Thus the contemplated countermodel is already present, not a missing proof.
- `Graph.fixedPoints_equal_of_wellFounded` supplies a sufficient condition for
  equality. `RegressDomains.CycleAndConverseBoundary` explicitly blocks the
  converse: every node can be intrinsic on a self-loop, giving equal fixed
  points without well-foundedness. Neither equality nor finite grounding at a
  selected node establishes global accessibility.

For a world-local application fix **one** `w`, use its existing-being subtype
as carrier, and restrict `R` and `O` to that carrier. The same polymorphic
schema applies; it does not require a new activation engine, a union of
cross-world edges, or a temporal interpretation. This is an instantiation
recipe, not a newly verified world-local physical model. In particular,
`O` remains an independently interpreted input: it must not mean “whatever
source the desired conclusion requires.” Graph sources (no incoming edge)
and intrinsic-power bearers are different predicates in these theorems.

The decisive missing bridge remains **ACT-GROUND**: an independently
characterized actual exercise, in a specified world and respect, must belong
to this least fixed point (or meet another independently defended condition
which entails finite grounding). That bridge would exclude source-free
active assignments by composition with the existing source theorem. It is
not established by monotonicity, an observed effect, link-cut sensitivity,
or the mathematical existence of least and greatest fixed points. Assuming
accessibility supplies a stronger sufficient background, not a defense of
that background. Conversely, the strongest structural rival can regard the
whole non-well-founded assignment as actual and treat the global structure
as its ground. The existing countermodel establishes consistency of the
encoded constraints; it establishes neither that rival's actuality nor its
metaphysical impossibility.

The merged #625 `UniqueFeedback.Controls` control further rules out using
solution multiplicity as a general objection to global constraints: its
sensitive Boolean equations have a unique solution without observational
selection. Those gates are not the pure borrowed-power transmission law,
so they are not substituted for a causal model. The existing
`CONVERGENT-ZENO-SCHEDULE` and `SUPERTASK-FINITE-PREFIX-NONUNIFORM`
controls concern mathematical scheduling and finite-capacity quantifiers;
neither supplies ACT-GROUND or a bound on real causal transfer. The #588
Night/capacity extension preserves that investigation's finite models and
does not establish this bridge either.

Even a defended bridge would initially give an original power in the chosen
respect. `PowerExistenceBoundary.Boundary` retains controls in which such a
source has external support of its existence, or is necessary and composite.
There is no passage here from an original exercise-source to an uncaused
whole being, simplicity or God. The exact root-premise delta is zero; the
no-infinite-per-se-efficient-cause premise, ACT-POWER, ACT-GROUND, ACT-LIMIT
and any Reaper recombination principle remain open. No source attribution,
new argument, result, Challenge or replacement definition is introduced by
this audit. Existing verification evidence is reused; no Lean checker rerun
can discharge the remaining interpretive bridge.

### A new limit test: the intrinsic source escapes to infinity

The verified finite-grounding theorem alone does not authorize us to take
an infinite limit of finite grounded causal histories and infer that the
limit is grounded. `CAUSAL-GROUNDING-LIMIT-SOURCE-ESCAPE` formalizes an
explicit countermodel to that additional *closure under limits* inference:

1. At truncation `N`, the only intrinsically powered node is `N`. Along
   successor links `N → N-1 → ... → 0`, each lower node has an **actual
   finite inductive grounding certificate** in that truncation.
2. For every fixed node `k`, all sufficiently long truncations power `k`.
   So the pointwise limit of the activity predicates is **all-on**.
3. For every fixed `k`, all sufficiently long truncations locate the
   source **somewhere else**. Indeed the source escapes beyond every fixed
   finite set of candidate nodes. The pointwise intrinsic-source limit is
   **empty**.
4. The limiting all-on state satisfies the unchanged local transmission
   equations. But it is not *inductively finitely grounded* with the
   source-free predicate: the new proof **imports**
   `FINITE-GROUNDING-HAS-SOURCE`, which extracts an intrinsic source from
   any such grounding certificate.

The mathematical lesson is the same one exposed by the infinite urn in
[the supertask study](supertasks.md): **the limit of grounded stages need
not be grounded under the same semantics**. It is a quantifier/witness
issue, not a contradiction in the stage-by-stage certificates:

> Each finite truncation has *some* source; therefore the infinite limit
> has a source.

That inference requires an additional uniformity, compactness or closure
assumption. Its failure is not evidence that the source-free all-on
**mathematical fixed point** is inconsistent. Conversely, the coherent
fixed point is not evidence that it is **actual derivative causal power**.
The repository explicitly keeps those semantics separate.

This exposes a sharper **ACT-LIMIT** obligation for #310: why should
metaphysically real exercise of borrowed power be representable by a
source-grounded derivation that is preserved under the proposed passage to
the infinite causal limit? A finite *uniform grounding-depth bound* would
block this particular escape construction; whether such a bound is true of
real essentially ordered causes needs an independent defense and cannot be
silently inserted as a theorem hypothesis. The countermodel also bears on
#311: distribution of already-actual goods or power along every finite
path does not by itself produce or explain the existence of the distributed
good at the source-free limit.

This suggests a sharper proof task than "all infinities are impossible":

1. Define a *per se* instrumental cause by its **essentially borrowed** power,
   not merely its temporal ancestry or observed activity.
2. Establish, without merely defining the desired conclusion, **why real
   instrumental causation must follow the inductive/finite-source semantics**.
   The finite-grounding theorem then entails that an all-borrowed source-free
   chain cannot ground a present act.
3. Challenge this bridge with the stronger cut-edge and global fixed-point
   models. Explain why their power should not count as genuinely derivative
   efficient power, or concede the limit of the proof.
4. Only then, if helpful, defend a bridge from a hypothetical chain to a
   *possible* Grim Reaper configuration. Distinguish logically consistent
   instructions, physically possible operations, and metaphysically possible
   causal networks; a paradox in the instructions by itself does not settle
   these modalities.

### Which reading of "cannot go on to infinity"?

The target premise is formalized as accessibility (`∀ x, Acc CausesAsCaused x`,
DEF-REGRESS-ACCESSIBILITY-READING). The Latin denies more literally that the
series *proceeds to infinity*: that there is an infinite series of causes each
caused as cause by the next (DEF-NO-INFINITE-DESCENDING-PER-SE-SERIES).
DISAMB-NO-INFINITE-REGRESS-READING keeps the two senses apart, and two results
relate them for every relation:

- `REGRESS-ACCESSIBILITY-EXCLUDES-DESCENDING-SERIES` (axiom-free): the
  accessibility reading implies the literal reading.
- `REGRESS-READINGS-COINCIDE-CLASSICALLY` (Mathlib, classical axioms): the
  converse holds too, so in classical logic the formalization is not stronger
  than the literal reading. The converse builds an infinite series from an
  inaccessible being by choice; it is not available constructively.
- `REGRESS-ACCESSIBILITY-ALLOWS-UNBOUNDED-DEPTH` (axiom-free): accessibility
  is well-foundedness, not finite depth. On the naturals with a top that every
  natural links to, every being is accessible, yet chains below the top have
  every finite length. Neither reading bounds how long a finite per se series
  may be.

These are fidelity checks on the formalization, not progress on the premise:
neither reading is shown true of any actual `CausesAsCaused`, and the
countermodels above refute both readings equally on the successor chain.

### What the grounding route still needs

`FINITE-GROUNDING-HAS-SOURCE` gives every inductively grounded being a source,
but not the accessibility reading. Two axiom-free results locate the gap:

- `GROUNDING-WITH-UNIQUE-CAUSE-YIELDS-REGRESS-READING`: if every being's power
  is inductively grounded, sources receive no per se link
  (DEF-SOURCES-RECEIVE-NO-LINK), and each being has at most one immediate per se
  cause (DEF-AT-MOST-ONE-IMMEDIATE-CAUSE), then every being is accessible.
- `GROUNDING-WITHOUT-UNIQUE-CAUSE-ALLOWS-REGRESS`: without the uniqueness
  condition this fails. One source links directly to every node of an infinite
  descending chain, so every node is grounded and the source is uncaused, yet no
  chain node is accessible.

Both are conditionals or countermodels; none of the three antecedents is
sourced or proved of real per se causes, so the premise stays open.

`KANT-WELL-FOUNDED-CAUSES-BLOCK-ALL-CONTINGENT` places Kant's local-causality
countermodel (`KANT-LOCAL-CAUSALITY-INSUFFICIENT`) in the same picture: in any
Kantian ontic model, local causality plus a well-founded `Causes` relation at a
world where something exists excludes every existent being contingent. The
conclusion is the negation of a universal; reaching a necessary being from it
needs excluded middle, and Kant's generic `Causes` is not `CausesAsCaused`.

## 4. Primary-source boundary and further objections

- **Pinned:** Aquinas, *Summa theologiae* I q.2 a.3, via
  `AQUINAS-ST-I-Q2-A3`, argues that removing the first cause removes the
  middle and the last; this is the very inference under challenge.
- **New pinned witness:** Aristotle, *Metaphysics* II.2 (994a),
  `ARIST-MET-II-2`, from the existing immutable Perseus Greek snapshot. Aristotle
  says that all terms of an infinite series of this kind would be intermediate
  and without a first there is no cause. The chapter treats several kinds of
  cause, so applying that statement specifically to the typed relation
  `CausesAsCaused` requires an interpretive step. The passage is **not** counted
  as a mathematical proof of well-foundedness.
- **Koons reading completed:** Robert C. Koons, *The Grim Reaper Kalam
  Argument* (author-hosted manuscript), §4, printed pp.14–16, with §3 and
  §5 context. The pinned witness and prior reconstruction are in
  [the #367 source audit](notes/causal-finitism-367.md#renewed-defense-audit-the-patchwork-bridge-2026-10-28).
  The ACT-TRANSFER reassessment below reuses that work.
- **Further research leads:** Nicholas Shackel, *The Form of the Benardete Dichotomy* (the unsatisfiable-pair
  diagnosis); Alexander Pruss, *Infinity, Causation, and Paradox* (super-tasks
  and causal finitism), and his 2025 essay *Grim Reapers and Logical
  Impossibility* (the effects of additional rules such as resurrection);
  Schmid and Malpass, *Benardete Paradoxes, Causal Finitism, and the
  Unsatisfiable Pair Diagnosis* (objections and replies).

**Frontier verdict:** the impossible Reaper schedule, finite schedule, infinite
local-transmission countermodel, cut-edge dependence countermodel, observation
selection lemma and finite inductive-source theorem are constructively proved
in their respective models. The escaping-source limit countermodel
(`CAUSAL-GROUNDING-LIMIT-SOURCE-ESCAPE`) is likewise verified.
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` remains **open**. The next
research slice is an independent defense of why *per se* efficient power has
the inductive source-grounding semantics and why that semantics survives the
physically relevant limit, not a Lean `sorry` removed by restating the target
as an axiom.

For the separate question whether an **endless temporal task can finish**, see
[supertasks and divergent series](supertasks.md). Its limit-endpoint model,
oscillating-output counterexample and fixed-cost divergence result do not
transfer automatically to simultaneous *per se* causal dependence.


## Typed per-se / historical distinction (#1112)

`STMT-INFINITE-REGRESS-IMPOSSIBLE-ONLY-IN-PER-SE-SERIES` keeps its original
source claim and frozen two-`Prop` declaration. That declaration is a
transcription of two assertions (`P ∧ Q`), not a proof that a causal history
is possible. The analyst sibling
`STMT-PER-SE-HISTORICAL-SERIES-DISTINCTION` instead constrains two relations.
Attribution of this new formulation is deferred.

`HistoricalLinksAreEssential H E` explicitly says that every proposed historical
predecessor is an essential-dependence predecessor. Given this dictionary and
`∀ x, Acc E x`, the existing
`RegressAccessibilityExcludesSeries.accessibilityReadingExcludesDescendingSeries`
excludes an infinite `H` descent by mapping each chain edge into `E`. Without
the dictionary there is a concrete same-member witness on `Option Nat`:

- Essential candidate links: `E y x ↔ y = none ∧ ∃ n, x = some n`.
- Historical candidate links: `H y x ↔ ∃ n, y = some (n+1) ∧ x = some n`.
- `E` is nonempty and accessible everywhere. Every historical member `some n`
  has the common essential predecessor `none` and historical predecessor
  `some (n+1)`. The chain `n ↦ some n` is injective and infinite; none of its
  historical edges is an essential edge in this model.

A first essential source exists in this witness, not in the definitions of
series or link. Replacing “each cause after the first” in the definition avoids
assuming that the target series already has a first. No transitivity axiom is
imposed on either primitive relation. Well-foundedness is the separate
hypothesis in the conditional, not part of what a link means. The witness
certifies compatibility of these exact relation constraints only. It does not
show a possible infinite past, actual causal history, or that every
per-accidens series is permitted. Separation of edge extensions alone does not
prove counterfactual independence of the causal powers of their endpoints.

The strongest conflation tested here identifies historical links with essential
links; inclusion alone already suffices to exclude the chain under essential
well-foundedness. No claim is made that these two choices exhaust accounts of
causation. The old exact controls
`SecundaVia.secundaViaNeedsPerSeOrder` and
`SecundaVia.secundaViaNeedsNoRegress` are imported and rechecked, preserving the
Nat successor models with respectively empty and successor essential links.
Thus neither the essential-link premise nor its no-regress premise can be
discarded from that general argument. The new compatibility witness strengthens
the empty-link control by making essential dependence nonempty on the same
historical members; it does not satisfy the omitted strong per-se ordering rule.
`RegressAccessibilityUnboundedDepth.accessibilityAllowsUnboundedDepth` is also
reused: arbitrarily long finite essential descents are compatible with
accessibility, whereas a single infinite descending chain is excluded. The new
historical witness supplies the latter chain for a *different* relation.

The stone/stick/hand and father/son examples motivate the intended distinction;
the first is sustained exercise of power, while the second's generation by a
father does not by itself say that the father sustains the son's present
exercise of power. These are intended readings, not a formal identification of
ordinary examples with the predicates. **OPEN:** interpreting essential links as
here-and-now dependence, their removal as loss of power, and historical links
as temporal succession needs explicit time/intervention vocabulary and an
applicability bridge. The existing `TemporalPrimaVia.Controls.descent` gives a
separate time-indexed control, already in the corpus; it is not silently
identified with this binary witness. Moving-as-moved and causing-as-caused also
remain distinct, connected only under their existing explicit link premise.
No root route, floor, no-regress input, or source-derived Challenge is changed.


## Old #310 attenuation acceptance reconciliation (2026-11-11)

The November 3 issue reconciliation predates [PR #1379](https://github.com/moritzbrantner/truth-core/pull/1379).
Its finite-attenuation mathematical item is now covered by that merged batch;
this audit introduces no duplicate attenuation theorem or changed causal meaning.
Evidence baseline: `8014a6806` (the attenuation files are unchanged from delivered
head `0453441ef869d0c8b9317ca356100b39e98ec8d1`). The complete earlier
[applicability walk](notes/contractive-borrowed-power-1378.md) remains authoritative
for its premises, controls and open interpretation burdens.

**Exact existing proof.** In
`TruthCore.Results.Causality.QuantitativeTransferPaths.finitePath`
(result `082838e6-d83c-4cbd-b3aa-e252d6af946c`), the local proof `decay`
derives `P x ≤ q^n * M` for every natural n at any node with no finite path to
positive input. Its final limit step uses
`Mathlib.tendsto_pow_atTop_nhds_zero_of_lt_one` and `ge_of_tendsto` to obtain
`P x ≤ 0`, contradicting `0 < P x`. This is the requested geometric
attenuation reasoning with the slightly weaker factor condition `0 ≤ q < 1`.
It is an internal step of the registered network theorem, not a separately
registered theorem accepting an arbitrary family of scalar estimates.

The full certificate requires a countable weighted network, nonnegative
weights/input/power, a common nonnegative finite upper bound M, summable weight
and weighted-power rows, a common row-sum bound q < 1, and the local balance
inequality `P ≤ s + weighted transfer`. Its positive conclusion is a finite
path to positive input, including length zero. It proves neither global causal
well-foundedness nor an intrinsically independent bearer. Calling a real chain
an instance still requires the quantitative/causal correspondence and these
premises; the mere word borrowed supplies none of them.

`TruthCore.Results.Causality.QuantitativeTransferPaths.vanishingTail`
(result `54e36212-e4d6-4a94-88a8-648ac39ec128`) separately proves the successor-chain
zero conclusion from exact local balance, a common absolute bound and vanishing
cumulative nonnegative transfer factors. Uniform strict fractional loss is a
sufficient mathematical route to geometric decay, not necessary for that result.
The batch also certifies the whole-assignment omission witnesses:
`halfFixed` (`16f89f72-5999-42d2-a9d8-e578f2183259`) permits uniform half-loss
with unbounded powers `2^n`; `nonuniformFixed`
(`b361eb10-4bc7-4cf8-a42c-28d45bc5d7aa`) permits bounded positive powers with
strict but nonuniform losses, and `nonuniformTail`
(`d1c3835a-f5c9-4acf-8664-aa7720ccbd45`) bounds every cumulative product away
from zero. `binaryFixed` permits bounded positive balance when total gain is
one. These are structural mathematical controls, not actual metaphysical models.
Finite grounded horizons remain available through the existing source-escape
certificate; they are not an infinite uniformly bounded lossy counterexample.

**Verification reused.** The original final-head [CI run](https://github.com/moritzbrantner/truth-core/actions/runs/42912864459)
passed corpus/Lean and all selected Comparator shards plus aggregate checks.
The existing result configs certify each named theorem separately. This
reconciliation changes no theorem, Challenge, binding, result status or premise;
no historical source is fetched and no repeat heavy verification is needed.
Computed context marks the finite-path mathematical statement proved and not
reaching the root. This is acceptance progress for model 4, with **no root
premise discharge**. It does not close the broader #310 issue.

**Remaining question and next discriminating step.** ACT-POWER, ACT-GROUND and
ACT-TRANSFER are independent open burdens. The strongest globally active rival
can retain conservative or asymptotically lossless transfer and a globally
obtaining non-well-founded assignment; this batch supplies no contradiction
with an accepted floor for that account. Finite shared-resource conservation
does not by itself force strict aggregate loss. The follow-up
[productive-store investigation](notes/productive-store-1378.md), merged in
[PR #1386](https://github.com/moritzbrantner/truth-core/pull/1386), already tests
finite resources and depletion: positive output in every natural interval is
compatible with decreasing discharge, while uniform demand requires an explicit
positive lower bound. Repeating finite-budget arithmetic is therefore not the
next test.

The useful remaining #310 task is to take one independently characterized
present exercise and its respect, state whether the relevant quantity is
instantaneous power, interval work, capacity or existential support, identify
the same resource and roster boundary, and defend or reject the abstraction to
a common bound plus vanishing cumulative gain. Test that abstraction against
the conservative/global rival and stored-resource exercise. A source of this
quantity still needs a separate bridge to existential independence; #311's
explanatory adequacy does not supply it. The provisional assessment is unchanged:
the bounded lossy class is conditionally excluded; actual all-borrowed per-se
exercise remains underdetermined. Revise this assessment only with independent
warrant for those applicability premises or a different discriminating argument.


**Remaining actuality branch inspected after reconciliation.** The existing
`BorrowedExercise.Certificate` already separates possession, exercise and
lending: the SAME exercise graph and occurrence assignment has an instrument
profile `capOccurs` and a secondary-cause profile `capAll`. The all-instrument
regress is explicitly certified; `SelectedCollapse` also shows that restricting
allowed scenarios changes this classification. Thus neither occurrence nor
lending, by itself, identifies the intended real borrowed capacity. A fresh
profile-switch model would duplicate those controls.

A materially different test is whether dependence in possession of an essential
power reaches dependence of its bearer. The existing
[essential-power investigation](notes/borrowed-exercise-741.md#does-derivation-of-an-essential-power-reach-the-bearer)
and attempt `8eee1ef4-39f2-4cc8-8e31-e7dde1134c0a` already isolate the exact
unmet node: externally grounded possession must be the SAME constitutive
actuality partly grounding the bearer's existence, with composition of those
grounding links and correspondence to the selected existential-support relation.
Inseparability of power and bearer alone supplies neither explanatory direction
nor that correspondence. A nature-first rival can treat a power as consequent
on the nature instead. This is an existing analyst argument, not a new sourced
reading or certified metaphysical theorem from this audit.

The existing `PowerExistenceBoundary.originalPowerBlocksEsseSupportIfItTransmits`
is the exact alternate conditional: esse-support is excluded if every such
support edge transmits this SAME power to a bearer with no incoming transmission.
It leaves the support-to-transmission bridge open. A mechanical input or an
energy ledger cannot silently provide it. For coordinator reassessment, the
next live node is therefore the constitutive-possession/esse-support bridge for
one selected essential power, rather than another fixed-point, budget or
profile-switch calculation. The repository has no independently warranted
identification of that selected power and those constitutive links in the
inspected records. It would be a separate interpretation/warrant assignment;
this reconciliation does not pretend its absence exhausts the parent question.


## ACT-TRANSFER reassessment for #310 (2026-11-11)

### What is already delivered

The November 3 issue comment's “§4 not pinned or read” item is superseded by
existing work, not a new source discovery here. The author-hosted witness is
[recorded](../corpus/passages/koons-grim-reaper-kalam.json), and the
[existing attempt](../corpus/attempts/pruss-koons-finite-history-reading.json)
and [#367 note](notes/causal-finitism-367.md) preserve its reading, rival and
formal follow-ups. This continuation reread the materialized, hash-checked
pp.6–16 and 18–22. The cached PDF title page identifies Robert C. Koons and the fuller title
*The Grim Reaper Kalam Argument: From Temporal and Causal Finitism to God*;
the corpus uses its short title and identifies it as an author-hosted manuscript.
No new historical claim or proof certificate is introduced.

`INDEXED-SIGNAL-REAPER` already derives the Reaper law from the jointly required
index bound, positive trigger, own-code emission and unchanged forwarding;
`GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` supplies the contradiction. The
omission controls preserve the other three rules when one is removed. These
are verified conditional mathematical results. They neither realize the rules
metaphysically nor derive them from arbitrary borrowed power. Repeating a
conditional with an opaque “possible network” premise would add no evidence.

### Does simultaneity itself defeat the strategy?

No such defeat follows from §4. Its CPNPP preserves a directed causal-power
pattern; unlike §3's spatiotemporal patchwork, its stated antecedent does not
require a metric/topology-preserving embedding of the original times. Thus it
would be too quick to say that a present simultaneous series cannot be used
because the illustrative Placers act successively. A defender can propose that
the original series supplies only the possible causal graph, while replacement
patches supply the Placer response and, where needed, its timing. This is the
strongest positive application to #310; it does not infer an infinite past
from a simultaneous chain.

That proposal still needs three different permissions:

1. **Framework interpretation.** The hypothetical present exercises must yield
   actual event-nodes in one possible world, with each selected upstream link
   having the p.15 meaning: an entity's power relevant to influencing the next
   event. A coherent assignment of activity values alone supplies no such
   event/power interpretation. If actual power exercises are admitted as events
   with these influence relations, that particular objection is answered
   conditionally. A mere relational resemblance is insufficient. The prior
   bearer/esse map remains a separate, already recorded gap.
2. **Uniform replacement.** For every node, not merely three named nodes, the
   chosen replacement and exact duplicates of its adjacent replacements must
   form a possible local event context. The Trio is Koons's positive proposal
   for this step (p.16). Moving from that example to every indexed role must
   preserve the relevant detector/register, the trigger and maintained signal
   content, and any required temporal ordering. Relabeling intrinsic
   index-sensitive positions or response powers is not automatically exact
   duplication. This is an uncompleted applicability argument, not a proof
   that the required local contexts are impossible.
3. **Countable assembly.** CPNPP supplies one world realizing all those patches
   in the selected graph. Intrinsicality preserves a power in an exact
   duplicate *if that duplicate exists*; it does not independently provide
   all duplicates' joint existence. Positive influence edges alone do not
   supply complete channel handoff or exclude relevant bypass inputs. Complete
   protected patches are the strongest proposed answer, but their preservation
   together is precisely what needs independent justification.

There is no additional requirement here to preserve the original chain's
spacetime metric under CPNPP. Conversely, a mathematical assignment of new
successive times would establish only scheduling, not any of the three modal
permissions above. No new scheduling theorem is warranted by this audit.

### A discriminating test: duplicating complete events or only capacities?

The phrase “complete protected patch” needs a precise scope. CPNPP's function
on p.15 selects events g(n), and the neighboring contexts must contain exact
duplicates of those same selected events. It does not merely require that for
each n some mechanism of the same general kind could occur beside some other
mechanisms. This makes a useful further test available without inventing a new
Reaper model.

Suppose the proposed patches include complete realized register traces. Assume
there is a duplicate-invariant projection from each selected g(n) to its output
`signal(n) : Option Nat` and issuance fact `issued(n)`, and that each possible
adjacent context preserves the full four local interfaces for those projected
values, including the same input/output handoff. The selection g then already
fixes ONE assignment on Nat. Local realizability for EVERY n entails the index
bound, trigger, emission and forwarding rules for this assignment. The existing
`IndexedSignalReaper.firingLaw` and `GrimReaperImpossible.grimReaperImpossible`
exclude that bundle. Under these strong trace-projection assumptions, the
uniform local-replacement antecedent fails before CPNPP supplies a world.
This is an explicit conditional reuse argument in prose, not a new certified
theorem or a verified source interpretation. In particular, no such projection
from Koons's event patches is established here.

If instead g(n) fixes only possession of a conditional response capacity,
possible local contexts can leave its eventual manifestation undetermined.
Then the proposed trace projection is unavailable, and that preceding argument
does not apply. This preserves the strongest positive reply: intrinsic devices
can have powers independently of what happens to activate them. But then
intrinsic duplication alone cannot be cited as preservation of a preselected
complete trace; the construction must separately show how the globally assembled
capacities enforce the required actual register interfaces and handoff. It
cannot silently alternate between capacity-only local feasibility and fully
manifested trace duplication.

This test sharpens the next source/application question rather than claiming a
new refutation: what exactly belongs to the selected EVENT, and which of its
actual boundary values are invariant under exact duplication? Koons's Trio
example does not explicitly give this event-to-register dictionary. A completed
dictionary could vindicate a capacity-based construction or reveal failure of
its local-context antecedent. Finite satisfiability does not settle either.

### Warrant comparison and provisional assessment

The positive argument has substance: ordinary recombination supports constructing
unfamiliar arrangements from understood capacities, and requiring local adjacent
contexts plus an already possible causal framework improves on unrestricted
juxtaposition. Koons's §5.1 defense of intrinsic powers addresses the objection
that duplication changes possession of those powers. His §5.2 also explicitly
requires persistent position/content; vanishing or recoding channels do not
refute that complete scenario. Its applicability should not be rejected merely
because the original target concerns present exercise.

The strongest standing rival accepts real intrinsic capacities and their
preservation in duplicates, while admitting only collections whose complete
responses and boundary conditions are jointly compatible. It can allow local
recombination without licensing every countable assembly. Its positive account
is compatibility-constrained realization of powers: dispositions do not license
an impossible global manifestation pattern. This is a proposed metaphysical
constraint, not a demonstrated possible source-free world. Its price is a
substantive nonlocal admissibility condition and an account of which histories
it admits; it cannot establish its own possibility by pointing at local
transmission equations. Koons's competing price is independent support that
his local-interface conditions suffice for countable joint realization. His
§5.3 recognition of causal provisos gives a reason to investigate restrictions
rather than dismiss every restriction as ad hoc; it does not establish this
rival's particular restriction.

**Provisional assessment:** the source-reading acceptance subtask is covered,
and the local-protocol-to-contradiction inference is already certified. The
present-chain transfer remains underdetermined by this evidence: neither its
metaphysical joint realization nor the impossibility of all such present
chains has been established. This retains the #367 judgment and corrects #310's
stale source status. No root premise changes. Mathematical finite compatibility
is inadequate evidence for unrestricted assembly: the existing
`GRIM-REAPER-FINITE-TESTS` even keeps each selected clause's full infinite tail
while showing no global assignment. This is not a modal refutation of CPNPP or
a failure of ordinary finitary compactness.

### Reassessment and next discriminating work

Rejected as duplicates or failed inferences: another finite schedule or
fixed-point model; a “possible Reaper world” flag that stipulates the disputed
transfer; deriving countable joint possibility from intrinsic possession or
finite compatibility; treating persistence as missing from the source; and
rejecting §4 solely because the initial series is simultaneous.

The next useful test is the **uniform local replacement obligation**: specify
one exact event-patch assignment for an arbitrary index, including which
register facts are duplicate-invariant and which remain conditional capacities.
For complete-trace patches, test the local-context antecedent against the
existing four-interface contradiction above. For capacity-only patches, defend
the passage to actual global interfaces and the independently warranted
recombination principle that preserves their handoff. If the
only argument for that principle is “otherwise the Reaper contradiction does
not follow,” it provides no independent discrimination. A warranted general
interface/gluing principle, or a concrete incompatibility among the required
local contexts, would change this assessment. Merely certifying another
conditional contradiction would not. The known event-to-esse abstraction burden
and separate loop exclusion would remain even after a successful assembly
argument. These are substantive reassessment points for the coordinator, not
claims that the whole philosophical question has been exhausted.
