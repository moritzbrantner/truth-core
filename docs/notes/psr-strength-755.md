# What each stronger PSR adds (#755)

This note maps PSR formulations in one arena and says what each step costs. The
theorems are `collapseCore` and `strengthMap` in
`TruthCore.Results.Explanation.PSRStrength.Solution`, over the vocabulary of
`TruthCore.Explanation.PSRStrength`. Both are zero-axiom. They establish conditional
consequence and the satisfiability of encoded bundles. They do not establish any PSR,
the metaphysical possibility of any model, or any premise on a root route.

No source claim is added. Pruss, Koons, Gale–Pruss, Leibniz, van Inwagen and Oppy
(#409, #365) were not read for this work, so no row below is attributed to them.
"BCCF" and "weak PSR" name formal conditions here, not those authors' exact theses.

## The relation being compared

`Arena.explains w r f` reads: at world `w`, the fact `r` is admitted as a reason why
the fact `f` obtains.

- **Ordinary language.** "The kettle boiled because the burner was on." A reason is
  a fact offered in answer to "why this?".
- **Examples and counterexamples.** Reasons that do not necessitate: an agent's motive
  for a free choice, or a stochastic setup for its outcome, on views that count them
  as explaining. Modal entailment that does not explain: `f` entails itself, and the
  `copy` model shows that this satisfies `FactPSR`, and so `ContingentPSR` and `NoBrute`
  (`ExistencePSR` needs `Coherent` as well, and weak PSR needs reflexivity).
- **Not the same as.** Efficient causation (`Ontic.Causes`, see
  `DISAMB-PSR-EXPLANATION-CAUSE`), modal sufficiency (`Necessitating`, see
  `DISAMB-PSR-REASON-NECESSITATING`), and conjunct-hood (`conjunct`).
- **Structural properties.** None is assumed. Transitivity, asymmetry and
  well-foundedness are absent. Factivity, necessitation, independence, distribution and
  contingent irreflexivity are separately named hypotheses, because which of them
  explanation has is the point at issue.
- **Generalization.** The map does not generalize from ordinary explanation to a
  metaphysical law. Each formulation is a hypothesis under test.
- **Competing accounts.** Humean or brute-fact views deny coverage; the necessitarian
  reading adds `Necessitating`; the nonnecessitating libertarian reading keeps coverage
  and rejects it. All three have a row below. Unificationist and contrastive accounts
  have no row: see the open axes.

## The incompatible core

`collapseCore` certifies that, given `ConjunctSound`, these seven members cannot all
hold at a world: `NoBrute`, `Factive`, `Necessitating`, `Distribution`,
`IrreflexiveContingent`, an aggregate `BCCFAt`, and a `Contingent` truth. Each member
is deleted by a model keeping the conjunct law and the other six, so the bundle is
inclusion-minimal. That is not minimum cardinality, and the core forces no choice of
which member to reject.

| Deleted member | Model | What survives |
| --- | --- | --- |
| Coverage (`NoBrute`) | `bruteTerminus` | A contingent terminus with no reason |
| `Factive` | `falseToken` | A reason token that is never true |
| `Necessitating` | `ground true` | A necessary ground with a nonnecessitating reason for a contingent fact |
| `BCCFAt` | `cofinite` | Unrestricted fact coverage, no aggregate of all contingent truths |
| `Distribution` | `mutualReasons` | A fact and its aggregate, each the other's reason |
| `IrreflexiveContingent` | `selfWhole` | A contingent fact that is its own reason |
| `Contingent` | `allNecessary` | No contingency at all |

A second bundle replaces distribution and irreflexivity with `ReasonIndependent`. It
is also inconsistent; `collapseCore` does not certify that this second bundle is
minimal.

## The strength table

Each row is a clause of `strengthMap`. "Bridge" is the extra hypothesis the valid edge
uses. World-relative formulations are read at the named world.

| Tested edge | Result | Bridge or separating model |
| --- | --- | --- |
| `FactPSR` → `ContingentPSR` | valid | none |
| `FactPSR` → `ExistencePSR` | valid | `Coherent` |
| `ContingentPSR` → `NoBrute` | valid | none |
| `ContingentPSR` → `ExistencePSR` | invalid | `ground false`: the necessary ground has no reason |
| `ExistencePSR` → `ContingentPSR` | invalid | `existenceOnly`: a contingent event has no reason |
| each member explained → whole explained | invalid | `history false`, every quality clause retained |
| whole explained → `ContingentPSR` | invalid | `history true`: the contingent law has no reason |
| each member explained → one `CommonReason` | invalid | `history` at `lawful` has none; `ground true` has one. Full `ContingentPSR` without a common reason is not tested |
| `NecessaryPSR` → `ContingentPSR` | valid with reflexivity | fails in `nonReflexiveBare` |
| `ContingentPSR` → `WeakPSR` | valid with reflexivity | fails in `nonReflexive` |
| `ContingentPSR` → `NecessaryPSR` | invalid | `modalGap` at `some true` |
| `WeakPSR` → `NoBrute` | valid | `Distribution` and `UnexplainedFacts`; dropping either fails (`modalGap`, `modalGapDiagonal`) |
| `StableReason` → reason at every world where true | valid | none |
| reason at every world → `StableReason` | invalid | `shiftingReason` (`□∃r` is not `∃r□`) |
| `LocalCausalPrinciple` and `ExternalCause` → `ExistencePSR` or `ContingentPSR` | invalid | `causeOnly`: an infinite causal chain, no reason |
| `ExistencePSR` and `LocalCausalPrinciple` → `ExternalCause` | invalid | `ground true` |
| `FactPSR` → `ReasonIndependent` | invalid where contingency exists | `copy A` has `FactPSR`, `Necessitating`, `Factive` over any `A` |
| `ReasonIndependent` → `Necessitating` | invalid | `ground true` |

The formulations are not linearly ordered: `ContingentPSR` and `ExistencePSR` are
incomparable, and quality conditions are a separate axis from scope.

## What a stronger version buys

- **Extending scope to necessary facts** adds a demand on necessary individuals,
  which `ground false` fails while meeting `ContingentPSR`.
- **Adding a whole** is not a further application of member coverage. `history false`
  explains every member and not the whole. To reach the whole, a domain must contain
  an aggregate; `cofinite` shows that fact coverage alone does not supply one.
- **Adding necessitation** is the step that makes contingency collapse a threat. In an
  extensional domain with entailment conjuncts (`Extensional`, `EntailmentConjunct`),
  weak PSR with factive, necessitating, distributing, irreflexive reasons excludes
  contingency at the world. The same domain without necessitation admits contingency,
  an aggregate and unrestricted coverage together (`extensionalGround`).
- **Weakening to possibility** avoids collapse only if a bridge is refused. Weak PSR
  yields `NoBrute` given distribution and diagonal facts, and extensional domains
  supply the diagonal facts and an aggregate. So the weak version's safety depends on
  rejecting extensionality or a reason quality, not on its modal position alone.
- **Requiring independence** is what separates a real reason from `copy`, which meets
  `FactPSR` over any arena. It is a quality condition, not more scope.

## Controls

Positive: `ground true` is a necessary ground with a nonnecessitating reason for a
contingent fact. The signature has no predicate for personal agency, so necessary
personal ground with free choice and necessary impersonal ground with an
indeterministic output are the same structure here, and no theorem separates them.
`history true` is an infinite history with a law as necessitating independent reason
for the whole; the law is itself contingent and unexplained there.

Negative: `bruteTerminus` is a brute contingent terminus. `history false` is a locally
explained, globally unexplained infinite chain.

## Surviving configurations

| Configuration | Survives | Smallest listed premise that eliminates it |
| --- | --- | --- |
| Brute contingent terminus | `ContingentPSR` fails, the rest of the core holds | `NoBrute` |
| Unexplained infinite history | member coverage | a reason for the whole, then `NoBrute` for the law |
| Lawful history with brute law | a reason for the whole | `NoBrute` for the law |
| Necessary ground, nonnecessitating reason | `NoBrute`, `ExistencePSR` | `Necessitating`, with the rest of the core |
| Domain with no totality | `FactPSR`, all qualities | a premise that an aggregate fact exists |
| Necessitarian, no contingency | the whole core except contingency | any contingent truth |

Coverage here favors no worldview. Theism's nonnecessitating ground and the impersonal
ground have the same row, and each theorem leaves its conclusion conditional.

## Open bridges and axes

- **Open bridges:** whether explanation is necessitating, whether a totality fact
  exists (`BCCFAt`), `Distribution`, `UnexplainedFacts`, and extensionality. Nothing
  here defends or refutes any of them.
- **Later axes:** the #942 extension below composes inquiry, contrast, a genuine
  normalized probability specialization, productive `Supply` and stopping tests.
  `ReasonIndependent` remains modal only; modal difference alone does not
  establish relevance.
- **Open interpretation:** none of these conditions establishes genuine
  explanation, productive applicability or a personal ground.


## Later axes composed (#942)

`PSR-LATER-AXES-MAP` (`PSRLaterAxes.interpretedMap`) imports and consumes the
original `strengthMap` and `collapseCore`, then connects the later results on
the same `Arena` vocabulary. The map is a collection of conditional constraints
and exact named controls. Different model carriers are not combined into one
witness. No PSR or explanatory standard is established.

| Axis | Certified connection | Existing results consumed |
| --- | --- | --- |
| Inquiry | With support coverage, the tracking bridge is equivalent to contingent-fact PSR. Their conjunction therefore reaches the aggregate collapse core when its other hypotheses hold. Meeting an inquiry demand alone does not: the critic retains a supported brute root. | `bridgeLadder`, `stanceMap`, `collapse_distribution` |
| Contrast | Uniform contrast implies per-rival contrast; the latter conflicts with a reason-closed founded account of a contingent target. The necessary-ground account is closed and two-way but fails contrast. The chain with its whole has per-rival contrast but no uniform reason. | `core_contrast`, `ground_closed`, `ground_two_way`, `chain_contrast_whole`, `chain_not_uniform_whole` |
| Probability | A normalized PMF and event-ratio conditioning specialize the existing per-reason ranking. With the stated base/field/selection conditions the earlier symmetry core rules out a contingent field member; it does not show that chance itself rules out contingency. | `perReason_fixed`, `core_necessary`, `core_pair` |
| Production | At actual target2, every all-necessary overlay meets contingent PSR and admits a reason-closed account. Single/plural Supply succeeds; branch/chain Supply fails. The chain even has unrestricted fact PSR. Plural Supply has no least graph foundation, and a rooted branch has no target Supply. | `overlay_all_necessary`, `single_supply`, `plural_supply`, `plural_no_least`, `branch_least`, `branch_no_supply`, `chain_no_supply` |
| Stopping | The contingent-only foundation norm permits two brute roots and an unexplained necessary ground; the unrestricted norm rejects that necessary stop. Neither is asserted. | `foundationNormTest` |
| Scope and witness identity | The earlier scope controls remain in the composed map, including failure of existential causal inference; the old modal/witness-strength rows remain unchanged. | `psrScopeBoundary`, `strengthMap` |

### Probability: what has actually been added

The ordinal rankings of #779 were explicitly **not** probability measures. The
new `chance` uses Mathlib's normalized `PMF` on the arena's own world carrier.
Its outer measure makes every event measurable. `chanceGiven r f` is the
intersection probability divided by the probability of `r`; `PositiveBase`
licenses conditioning by every base member, and `Raises` explicitly requires a
positive denominator. A positive denominator says nothing about actual truth.
`ProTanto` and `NetSelects` retain their separate truth and admitted-reason
clauses.

The finite control puts mass 3/4 at world0 and 1/4 at world1 of the existing
necessary-ground arena. The source fact is true at both and at every other
world. At world0 the target is true and highest-ranked. At world1 the source
and rival outcome are true, the target is false, and the source is admitted as
a reason for that rival; the rival has positive probability 1/4 but is not
net-selected by the fixed ranking. Thus demanding highest-probability selection
of **every** actual outcome is stronger than allowing probabilistic explanation.
No theorem says the admitted reason is adequate.

A fact true at **every sample world** has probability one, and conditioning on
it leaves every outcome probability unchanged. This prevents probability
raising by that truth event alone. It does not follow from mere modal necessity
at the actual world when the PMF may charge inaccessible worlds. An application
to `NecessaryAt` would need a support/accessibility bridge. In the concrete
control accessibility is universal and the source fact is globally true.
Conditioning on its existence is distinct from conditioning on a contingent
act, exercise or enabling condition: none of those is excluded by this result.

The point-mass control gives the rival probability zero while it remains true
at accessible world1. Probability-zero therefore is not encoded as
impossibility. The PMF is a mathematical input; objective propensity,
epistemic credence and real-world applicability are **OPEN**. Association and
probability ranking are not causal production.

### Productive and personal boundaries

The productive comparison reuses the exact #735 groups, intrinsic contributions
and actual target2, through #750's `overlay`. This projection treats event
existence facts as facts and graph contributors as admitted reasons; its
applicability to existential or metaphysical explanation remains **OPEN**.
The all-necessary overlay changes the modal status of bearers without changing
the actual graph. Its contingent PSR is vacuous, which is why the separate,
nonvacuous `FactPSR` chain control is included: every actual chain member has a
successor reason, and there is still no intrinsic contribution from which
inductive `Supply` can be derived. An admitted reason and productive supply
are different conditions. Existing #735 background/exercise verification stays
in its own certificate and is not promoted to explanatory adequacy here.

No positive personal-versus-impersonal discriminator is available in this
signature. The same `acting` frame has a necessary base, a contingent outcome
and all four tested choice marks with either value of the supplied personal
flag. The map proves those exact named controls; it does not assert that
personal and impersonal agency are equivalent. A substantive discriminator
would require an independently interpreted account of agency and a bridge
connecting it to explanation or production. Merely adding a personal flag
would stipulate the requested distinction. This is the remaining vocabulary
and philosophical blocker, rather than a missing proof search.

### Premises, sources and proof boundaries

All hypotheses of a conditional row remain inside its explicit quantified
statement. In particular, support coverage and tracking, aggregate existence,
necessitation, contrast, foundedness and necessary-base/selection/field clauses
are not silently established. The positive-base condition in the probability
row licenses interpretation as conditioning; the imported order-theoretic core
actually holds without that side condition. No claim is attributed to a new
source and no previous source interpretation is changed.

The new certificate closes no root premise. The root frontier remains subject
to the computed `frontier-diff`; its eventual PR records that exact delta.
The attempt `ATTEMPT-PSR-LATER-AXES-942` preserves the rejected identification of
ordinal favouring with probability and the remaining support, exercise,
relevance, agency and adequacy bridges.
