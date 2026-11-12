# Critical-spine dependency map (2026-11-12)

Linked from [the modal spine handoff](modal-spine.md). Working root:
`STMT-GOD-EXISTS` (8626f8a5). Nothing here establishes a premise; it records
which registered solution-present arguments need which premises.

Audited main: `d98066db300d5b02c2062c2a55d622a237ace49b` (includes #1534
and #1499). This is a dependency refresh, with no Lean edits or new source
attributions. #1468 is outside this assignment. Shared conventions resolved at
`15f348b072188255da837578eaafc8a98f12fdf0`.

## Method and its boundary

Graph: every corpus argument with a solution-present result record, as an AND/OR graph (an
argument is an AND over its premises; the arguments concluding one statement
are its OR alternatives). Two readings of "P is unavailable":

- **Strict expansion.** Only statements with no verified derivation may be
  accepted as leaves; every other statement must be derived. Derivability is
  the least fixpoint over verified arguments (the graph has cycles, so only
  well-founded derivations count). Removing a set S of statements means no
  member of S is a leaf or derivable. This answers "which derivations need P".
- **Lenient.** Any statement may be accepted as an open premise. P removed
  blocks only arguments that list P directly; the derivations behind other
  premises are irrelevant.

Under either reading, a derivation that runs through P is *support lost* for
its conclusion, not a refutation of it. Removing P neither establishes ¬P nor
refutes P's consequences, and no row below is a claim that P is false. Shared usage and
node degree are not indispensability: the tables count surviving OR-alternatives.

## Current stage-one join

`STMT-NECESSARY-CONCRETE-UNDERIVED-AT` (0bdcf366) has **nine** registered
support alternatives. Existing five:

| Argument | Joint premises |
|---|---|
| df542c04 | population, AGWF, contingent grounding, F1, J1, J2, EM |
| d45dba04 | NCAT, F1, J1, J2, EM |
| 36c6b111 | NCAT, AGWF, J1@w, coverage, EM |
| 9de79a41 | NCAT, AGWF, J1, coverage, EM |
| 9d8798ea | population, AGWF, contingent grounding, coverage, EM |

#1530 adds these four in `TruthCore.Results.Causality.ClosedGroundingRoots`:

| Argument / theorem | Joint premises |
|---|---|
| c285b2d8 / checksClosed | population, CCR, contingent grounding, F1, J1, J2, EM |
| f62e68f6 / underivedOfCoverageClosed | population, CCR, contingent grounding, coverage, EM |
| e099de52 / underivedFromNecessityOfCoverageClosed | NCAT, CCR, J1, coverage, EM |
| f8661716 / underivedFromNecessityOfActualCoverageClosed | NCAT, CCR, J1@w, coverage, EM |

CCR is `aca3baa1-9be6-4720-a53d-22050e638561`,
`ClosedGroundingCollectionsRooted m w`: every collection of actual CONCRETE_6
closed under its **direct actual concrete** grounds and containing no actual
concrete root is empty. NECESSARY_2 is the selected-world modal reading;
coverage explicitly transports actual rootedness to admitted worlds.
A root here may still have abstract or unmodelled suppliers.

AGWF (82cfaf26) implies CCR through argument 31b14428, theorem
`ClosedGroundingRoots.closedRootedOfWF`. The converse fails in the registered
direct-root-grounder control (result 66b54b88): endless chains and rooted cycles
can satisfy CCR. Foundation only through intermediaries can fail CCR; do not
silently replace direct grounding by ancestry.

CCR also follows conditionally from borrowed reality 45890c84 **and** the
concrete-supplier bridge b28f3a70 (ee5a7fb8 / closedRootedOfBorrowed), or the
uncalibrated uniform attenuation bundle f3158145 (feb28c90 /
closedRootedOfAttenuation). These are additional open commitments, not warrant
supplied by the theorem. Reuse attempts 4da08bd8 and 14fb7669.

J2 (d149d238) has derivation fe4b5ec7 from F1 (2b20b5af),
AGWF and no-novel-edge bd983df2, and the newer graded derivation 96acab66
from 40ce286d and 78945dde. Thus checksClosed **retains** the stronger
foundation dependence through J2; the three CCR coverage routes bypass it.
CCR does not replace J2's union-well-foundedness or asymmetry.

The old single-premise-cut and two-premise-cut lists are withdrawn as current
claims. In the current least-fixpoint graph neither AGWF nor finite rank is
indispensable to the join. Even removing AGWF and CCR together leaves the join:
d45dba04 can obtain J2 through the graded derivation 96acab66,
without either removed node. The least fixpoint does not create support from
a cycle alone. This is a structural bypass, not independent warrant.

Abbreviations: population 56f68b40; contingent grounding c71c068c; NCAT
b19ffd92; J1 dd41c165; J1@w 84751fc2; coverage df42581f; EM ee4ab504.

## Direct routes and existing connection

db2dead0 and c63f3afa conclude da3facd6 without the join, J1, J2,
coverage or F1. Their own asymmetry and grades-to-maximum obligations remain.
The #1514 projection 92ab7c94,
`TruthCore.Results.Causality.NecessaryClassicalGodRootGodExists.godExists`,
connects that classical root to STMT-GOD-EXISTS; it is an assembly, not an
independent defense of the root. Earlier route-cost/count reports are historical
and are superseded by the current graph below.

## Current root impact

Twelve root arguments: the earlier ten (ed7c588a, 678ff65f, 661ce61d,
fd1f7e75, beec1dc1, 0a639ec4, 1c154f2f, 72391d4d, 5e8e6054, 92ab7c94),
plus #1522's esse-only siblings fc46b7f9 and 3367bf93. Their exact theorems are
`TruthCore.Results.Causality.GradesAtBeingRoutes.directEsseRootGodExistsAtBeing`
and `existenceOnlyGodExistsAtBeing`. They use e4e6b0cd rather than all-respects
grades 6c27657f. Attempt bc71bfe8 preserves the declined 1c154f2f sibling and
its unresolved sense passage; do not count that sibling as registered.

Strict-expansion recomputation on this baseline:

| Removed statement(s) | Root arguments surviving |
|---|---|
| 82cfaf26 | 12/12 |
| a4d3261a, 3b2d2d46 | 12/12 |
| 376d6a5a | 3/12 |
| d5a94eb1 | 3/12 |
| aca3baa1 | 12/12 |
| 82cfaf26, aca3baa1 | 12/12 |

The transfer and “more such” cuts leave prima via ed7c588a and both esse-only
siblings. Their additional premises remain explicit; surviving a cut is no
philosophical refutation or discharge.

#1525 is merged, not pending. Argument 69affa96, result
778f2b9f-f177-4de8-b53e-4882cdaafe5b, theorem
`TruthCore.Results.Causality.NecessaryClassicalGodRootAtFirst.derive`, supplies
da3facd6 to projection 92ab7c94 using first-being priority 61ad11f3 instead of
independent universal priority 3b2d2d46, with the same 22 other premises.
It uses POTENCY_2 and PRIOR_1, plus the explicit GOD_1 → GOD_4 naming bridge
1ec205ed. The legacy a4d3261a POTENCY_1 link is not interchangeable with it.

61ad11f3 is still conditional: composition uses 8288ff1e (first being has some
act), 3d99779b (act plus potency makes composite), ca07cae9 (composite has a
distinct cause), e0088de9 (perfection cause to efficient cause), and e078f07b
(efficient cause is prior). Those warrant questions survive the bypass.
Reuse attempt e432c07c and its verification evidence. No new certification is
claimed by this map.

## Coordinator handoff: next targets, in owner order

These are assignment briefs, not investigations begun by this refresh.

1. **#1518/#1519 — transfer and weakest sufficient forms.** Root bottleneck:
   376d6a5a / d5a94eb1. Reuse the current #1516 ladder
   376d6a5a ⇒ d0fc96b7 ⇒ 4ccb319f ⇒ 4a5a43a5, preexistence 64498e7e,
   `TruthCore.Results.Case.Catholicism.CauseOfBeingHasBeing.causeOfBeingHasBeingOfAgency`
   and `causeOfABeingHasBeingOfPreexistence`, plus attempt c0c90cee.
   First reconcile #1518's branch with main: cffad050, 2c0b9bd7 and proposed
   route 5d2b7c6e are **absent from this baseline**, so their reported 11-route
   experiments are not current-main evidence. #1519 item 2 is already delivered
   in #1522 (two siblings, verum exception, declined sense passage); retain its
   accepted boundary. Item 1 remains the consumer audit after the weakening
   lands. Desired change: exact weaker inputs or justified strong-version
   annotations, without assuming preexistence alone breaks the bottleneck.
2. **#1553 — actual grounding.** Reuse 29398f60 /
   `TruthCore.Results.Causality.ClosedGroundingRoots.necessaryConcreteOfClosedRooted`
   (result 3cc1a964), CCR aca3baa1, contingent grounding c71c068c and controls
   66b54b88. Compare actual direct-grounding applicability, beginningless
   contingency, non-concrete explanation and intermediaries-only foundation.
   The discriminating question is warrant for CCR or its borrowed-reality
   supplier bridge, not another proof that AGWF entails a root. Carry #487's
   residual configurations; no source attribution from unread rival leads.
3. **#1554 — underived existence.** Target 0bdcf366. Reuse f62e68f6 /
   `ClosedGroundingRoots.underivedOfCoverageClosed` (result 1a2669d8),
   e099de52 and f8661716; compare coverage df42581f, actual J1 84751fc2,
   full J1 dd41c165 and J2 d149d238. Investigate actual-to-other-world
   transport/no-contingent-ground warrant. Per-world acyclicity does not
   establish union well-foundedness; an actual root is not automatically
   necessarily underived. Reuse #518 and the necessarily-underived-minimal-bridges
   attempt; compactness remains #484's ownership.
4. **#1459 — intentional creation.** Reuse #1458 and the
   `CausalExistenceWilling` declaration in
   `TruthCore/Case/Catholicism/DivineLoveBridge.lean`. Neither a registered
   statement under that declaration name nor the issue-linked creative-goodness
   note is present on this baseline; reconcile #1458 before treating them as
   corpus reuse evidence. Determine an
   independently motivated causal-to-volitional bridge or weaker sufficient
   premise. Distinguish possessing will from exercising it and necessary
   emanation from intentional willing. This refresh supplies no new bridge.

Maintain a second, distinct rival-worldview family alongside this spine work:

- **#1505 Wielenberg:** use the issue question names Q-MORAL-GROUNDING and Q-MORAL-SUPERVENIENCE
  as orientation (not registered statement IDs here), and reuse
  `TruthCore/Metaethics/SupervenienceProfiles.lean`. Test the positive
  necessary-norms-plus-natural-facts making account on pain and parental duty,
  with #1460/#371 as the named root bridge. Mapping fit remains an explanatory
  question; no causal impotence refutation follows from being non-natural.
- **#1508 moral authority:** use question names Q-NORMATIVE-REASONS and Q-MORAL-AUTHORITY
  as orientation (not registered IDs here), and reuse
  `TruthCore.Ethics.HardCaseTyped` and
  [natural goodness and authority](natural-goodness-function-and-authority.md).
  Compare reasons for an agent with directed standing to demand; test the
  alleged extra norm on both Wielenberg and authorial authority (#1460/#371).
- **#1500 companions in guilt:** reconcile draft #1502 before assigning proof
  work. Reuse f56b2ee7-c69e-5e3b-85b0-e671d907ba58 (thin F6),
  2ca463c2-bd1f-5a13-a395-0e2c57a5ad8f and
  `EpistemicAuthority.authorityFromAnswerability`,
  `goalRelativeExcludesAuthority`; preserve Olson's functional alternative.
  A strong epistemic witness still needs a bridge to moral instances (#933).
- **#1532 parity:** reuse PP-01's #1526 and STMT-NOTHING-ORIGINATES-ITSELF;
  PP-02 stays with #1500 and PP-05 with #1508. Require the same proponent,
  causal/normative sense and relevant conditions before alleging inconsistency.
  Classification alone closes no premise.

## Verification and reopening

No premise change: no statement, argument, result, Challenge, source or
closure rule changed. Claim/type self-sweep checks the map against registered
premise lists and existing theorem types; prior proof evidence is reused.
The graph counts are structural solution-present counts, not newly executed
Lean/Comparator/NanoDa evidence or a semantic challenge of new metaphysical
claims. Parent integration should challenge any stronger philosophical judgment.

Recompute after #1518 or any root-argument/CCR/transport change lands. In
particular, do not combine branch-only transfer experiments with the twelve
current-main alternatives. The remaining work is the ordered briefs above,
not an unresolved dependency-map implementation.

Computed frontier delta against the audited main: open root premises
479 → 479 (340 bare, 93 supported, 46 stated); support alternatives 373 → 373;
lowest-cost diagnostic 16 → 16; added alternatives 0; no change.
