# Natural goodness: function, due perfection and practical authority

This #369 slice distinguishes positive proposals and their remaining bridges.
It adds source commitments, not a proof of moral realism, an additional
verified result, or a claim that a complete rival has been eliminated.

## Witnesses read

The following complete pinned ranges were materialized and read before these
readings. The manifest retains the exact edition, immutable revision and blob;
the quotations below are only short identifying phrases.

- `ARIST-EN-I-7`: *Nicomachean Ethics* I.7, Greek Perseus edition
  `urn:cts:greekLit:tlg0086.tlg010.perseus-grc2`, especially
  1097b22–1098a20; the whole chapter supplies finality/self-sufficiency and
  the function argument's context. The new selector uses the existing
  `ARIST-EN` snapshot, not an unpinned modern translation.
- `AQUINAS-ST-I-Q5-A1`: the complete Leonine/SCTA article, including ad 1.
- `AQUINAS-ST-I-II-Q94-A2`: the complete Leonine/SCTA article, including ad 2.

The materialization commands are `python3 scripts/source_evidence.py materialize`
followed by the passage ID. Source integrity identifies the consulted text;
it does not settle the interpretation or truth of the account.

## What the positive argument actually supplies

Aristotle first asks what the specifically human function is; he does not
simply identify whatever happens to be preferred with human good. He contrasts
vegetative and perceptual life with rational activity, distinguishes a
practitioner from a good practitioner by excellence of exercise, and concludes
with excellent activity of soul across a complete life. Thus the positive
proposal offers a standard capable of correcting a current preference: ask
whether the agent's activity realizes the appropriate excellence of its
characteristic function. The analogy is a proposed reason for this account,
not a Lean proof that humans have that function or that distinctively human
activity is automatically normatively superior.

The exact new readings are deliberately limited:

| Reading | Bound type, with primitive predicate arguments suppressed | What it leaves open |
|---|---|---|
| `STMT-FUNCTION-EXCELLENCE-NECESSARY` | `∀ x r f, ExerciseOfRole x r → HasFunction r f → GoodQuaRole x r → ExcellentExercise x f` | Which roles/functions are appropriate and which excellence standard is correct. This assesses an exercise, not the claim that a skilled practitioner always acts well, and implies no moral verdict on the person. |
| `STMT-HUMAN-GOOD-ACTIVITY-CONDITIONS` | `∀ life, HumanGood life → RationalActivity life ∧ VirtuousActivity life ∧ CompleteLife life` | Function identification, virtue ordering, sufficiency, an actual happy-life witness and practical authority. |
| `STMT-ULTIMATE-DUE-PERFECTION-REQUIRED` | `∀ x, ¬ UltimateDuePerfection x → ¬ GoodSimply x` | What perfection is due, whether anything lacks it, and the positive/converse directions; no classical contraposition is silently added. |
| `STMT-REASON-REGULATED-INCLINATIONS-NATURAL-LAW` | `∀ i, HumanNaturalInclination i → RegulatedByReason i → PertainsToNaturalLaw i` | What correct rational regulation consists in and why it is authoritative. |

`VirtuousActivity` in the second type means activity according to the
appropriate virtue, with Aristotle's best/most-complete qualification where
several virtues are at issue. The formalization does not independently model
that ordering. The source condition is preserved as the predicate's stated
meaning, rather than advertised as a theorem about arbitrary excellence.

Aquinas' q.5 ad 1 is an important control on the positive proposal. First
substantial actuality makes something *being simpliciter*, but ultimate due
perfection is relevant to *good simpliciter*. Having some actuality is not
therefore already an all-things-considered verdict of excellence. The existing
`GoodnessIsActualityReading` is explicitly **per perfection** and already says
its type does not formalize the ad 1 distinction. No repair or strengthening of
that existing claim is warranted. This slice adds a sibling reading instead.

The q.94 ad 2 qualification also matters: natural inclinations, including
concupiscible and irascible appetite, pertain to natural law **insofar as
regulated by reason**. Reading it as approval of every actual urge would drop
a source condition. Conversely, merely defining correct reason as conformity
to the desired conclusion would not defend the account.

## Symmetric comparison of replacement accounts

The source-backed naturalistic proposals and their precise locators are already
recorded in [the naturalistic-realism comparison](../naturalistic-moral-realism.md).
They are affirmative rivals, not the denial of evaluative facts.

| Shared question | Function/teleological account in this slice | Railton/Boyd's existing naturalistic proposals | Attitude/plan-based alternative |
|---|---|---|---|
| What fixes an assessment? | Appropriate function and excellence; for Aquinas, due ultimate perfection and rationally ordered human goods. | Railton: objective interests and a distinct impartial rightness criterion. Boyd: human goods and sustaining homeostatic mechanisms. | Endorsement and reason-sensitive practical commitments may fix standards rather than detecting a mind-independent human end. This describes a rival option, not a new historical attribution. |
| Can present preferences be wrong? | Yes under the proposed appropriate standard; establishing that standard remains substantive. | Yes; existing cognitive-error models witness the formal compatibility, and the source theories propose fallible correction. | A sophisticated plan-based account can reject incoherent or ill-informed endorsements; it need not endorse every urge. Whether that earns robust stance-independent correctness remains disputed. |
| What remains to be defended? | Objective function assignment, why the human function has the proposed normative priority, warranted virtue/ordering and correct reason. | Adequacy of interests/cluster and causal access; the impartial criterion or normative role is not derived from biology alone. | Why these endorsements or constraints have authority and whether the earned semantic/normative resources suffice. |
| Does this supply categorical authority? | The first precept gives a sourced practical commitment, not a consequence proved from role-success or bare actuality here. | The recorded accounts give substantive reason proposals; neither their natural criteria nor the current finite models entail every agent has a universal instrumental reason. | Guidance follows under explicit normative commitments; deriving an ought from a purely descriptive factual constraint is not supplied. |

No column receives an aggregate score. A sourced answer is an answer even
when its defense remains open. A model of encoded behavior or error is not an
explanation proven adequate in reality. Conversely, independence from present
approval is not the same as independence from every fact about human psychology.

## Exact reuse and rejected duplicate proofs

- `TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability.goodnessIsActualityFromDesirability`
  already derives `GoodnessIsActualityReading` from the three recorded
  good/desirable, desirable/perfect and perfect/actuality biconditionals.
  `premisesNeeded` records their omission controls. Their fidelity and truth
  remain open; this source batch does not replace them with an analytic definition.
- `TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent.railtonConsistent`
  and the corresponding `BoydConsistent.boydConsistent` already witness the
  recorded fragments with a right/good act lacking a universal instrumental
  reason link. Their strengthened ascription results require genuine ascription
  witnesses. Repeating a generic good-does-not-entail-reasons model would add no
  new constraint.
- `DESCRIPTIVE-PLAN-BOUNDARY` and the existing plan-state work already isolate
  descriptive support from normative guidance. No static supervenience or
  factorization theorem was manufactured for this slice.

The next decisive issue is the independent warrant for the human function and
its appropriate standard, followed by the practical-authority bridge. The
candidate `NATURAL-GOODNESS-HUMAN-FUNCTION-AUTHORITY` keeps that investigation
explicit. It does not assert that the bridge is false or that the opposing
view has already answered every question.

## Premise and verification boundary

Intended and actual root-premise change: **none**. All existing root-route
leaves remain open on the same routes. The four new readings are attributed
commitments, not established premises or argument results. There is no new
Challenge/Solution, inference edge, result or Comparator certificate because
no new argument is advertised.

The three new source-reading modules elaborated with no diagnostics through
the shared Lean service at preview `de591c1d405b7279d470d06d4ebb1160e61f78ad`;
combined exact-content SHA-256
`b30edcdda8303cdb09e8cb38ae5b6c7a822ff9e3ffc0c3ddf7527797525658c0`.
Final CI checks the delivered imports and corpus. Existing proof evidence is
reused rather than rerun for unchanged results.

## End-to-end adequacy reassessment (#563, 2026-11-10)

Draft for the coordinator's independent semantic challenge. Evidence baseline:
`fd93f6387` (origin/main). This is a semantic/reuse checkpoint, not completion
of #563 or a newly certified moral argument.

### Criterion and its strongest rival reading

The defensible methodological demand is **scope accountability**: an account
advertising an explanation of preference-independent reasons for every human
must identify its human domain, applicable standards, normative connection and
stopping points, and address relevant defeaters. Unanswered questions within
that advertisement count against completeness; disputed proposed answers remain
open rather than absent. This is justified by the content of the advertisement:
a classification of acts alone leaves its explicitly advertised agent/reason
question unanswered. It does not prove that any such reasons exist or that
all adequate morality must explain reasons in this sense.

The stronger draft demand that every complete account of *categorical morality*
must supply end-independent reasons is contested. Railton's recorded distinction
between obligation and instrumental reason is a positive counterproposal to
that demand, not an admitted failure of his rightness criterion. A realist may
hold a wrongdoer obligated while denying that compliance serves the wrongdoer's
ends. An expressivist may explain obligation through planning commitments and
reject the further realist explanatory demand. To exclude either reply one
needs a defended moral-obligation-to-reason thesis and an argument against its
replacement account. Neither follows from the word “complete.” Preserve these
as research alternatives, without silently identifying moral obligation,
pro-tanto reason, decisive reason, motivation and instrumental advantage.
These prose alternatives are not new formal senses or corpus propositions.

### Exact terms and one explanatory path

Read the existing shared answer-map table in
[the naturalistic comparison](../naturalistic-moral-realism.md#shared-answer-map)
along the Catholic column: Q-MORAL-GROUNDING → Q-NORMATIVE-REASONS →
Q-MORAL-EPISTEMOLOGY. This is a sequence of proposed answers, not a registered
inference chain. `CatholicNaturalLaw` in `TruthCore/Comparison/Metaethics.lean`
conjoins ontological goodness/actuality, privation, truth-aptness, a particular
error reading and the first practical precept. Conjunction supplies no bridge
between them. There is no agent-indexed obligation in its first precept.

| Load-bearing term | Actual formal content and remaining semantic burden |
|---|---|
| Good in a respect | `GoodnessIsActualityReading`: supplied GoodIn/Has biconditional on being/perfection; neither human function nor practical authority is its body. |
| Ultimate due perfection | Seed `1d35dc3b-f8af-5362-b53b-23651f89f9de`: absence excludes GoodSimply. UltimateDuePerfection and GoodSimply are supplied predicates; due-ness, existence, converse and categorical reasons do not follow. |
| Function/end and human nature | Existing function reading gives a necessary excellence condition for a specified role; human-good reading gives necessary rational/virtuous/complete-life conditions. Function assignment, appropriate virtue and its ordering remain substantive. A biological regularity or distinctive capacity alone does not identify its normative priority. |
| Rational regulation | q.94 ad 2 requires a supplied RegulatedByReason predicate before inclusion in natural law. Its correctness and authority are not definitions proved by that implication. |
| Practical good and “to be pursued” | `FirstPreceptOfNaturalLawReading Good Evil Pursue Avoid` is `(∀ a, Good a → Pursue a) ∧ (∀ a, Evil a → Avoid a)`. All four predicates are primitive parameters, explicitly documented in Article2.lean and definition `4e86d1ed-86f3-5ed2-b484-78a012f0bfa1`. |
| Applies / reason / obligation / categorical | The first-precept signature has no human or preference coordinate. The naturalist `Sig.Reason` is an independent agent/action predicate. RightWithoutUniversalReasons means `∃ x a, Right a ∧ ¬ Reason x a`; it does not itself encode motivation or quantify over preference changes. |
| Explanation / adequacy | No Lean predicate here defines philosophical adequacy. AnswerMap.answers records availability, says records the proposed proposition, CommittedAt requires both. None certifies warrant, explanatory direction or completeness. |

The current bottleneck is therefore between practical verdict and its authority
for the particular human. The strongest rational-nature proposal says that
practical standards apply constitutively to humans as rational agents, including
those who reject the ends, rather than only to voluntary participants. Its
positive rationale is that practical deliberation already answers to standards
of reasons, so rejecting a desire does not remove that answerability. The
objection is precise: standards necessary for successful deliberation may
specify excellence *qua deliberator* without establishing moral priority over
self-interest or duties toward others. A skeptic can deliberate effectively
about harmful ends. A successful reply must establish the relevant other-regarding
content and authority, rather than define rationality as agreement with it.

Eternal-law grounding is a proposed further explanation in the linked source
comparison, not a component of this first-precept type or a derived authority
bridge. This audit found no eternal-law body in the inspected natural-law
bundle/definitions; it does not claim an exhaustive corpus absence. Do not
import divine jurisdiction from `NaturalReasonAuthority.AuthorityProfile`:
that primitive means entitlement of a standard to judge a practice move, not
an agent's moral reason. Nor does belief-specific `BeliefAnswerability` in
`Logic.EpistemicAuthority` transfer to action; its documentation explicitly
restricts it to belief. The two deferred #1376 routes remain unregistered.

### Conditional bridge test and its limitation

A development test uses the actual first-precept definition with a separate
application premise `∀ h a, Pursue a → Reason h a`. From `Good a`, implication
elimination yields `∀ h, Reason h a`. This exposes exactly where universal human
authority enters. It supplies no preference semantics, normative explanation,
decisiveness, applicability defense or proof of that application premise.
Omitting application permits Good/Pursue true and Reason false; omitting Good
permits all four practical predicates false with Reason false. Both retain the
first precept. Thus first-precept consistency alone cannot supply the target.
These are elementary interpretations described here, not new registered or
Comparator-certified results. No new frozen Challenge is warranted for this
reuse-level observation. The genuinely informative next formal target is a
specified rational-agency argument for the application premise, including an
other-regarding norm and a harmful-but-effective deliberator control.

### Positive rivals under the same questions

| Account | Positive answer and warrant proposal | Discriminator and current classification |
|---|---|---|
| Rational natural law | Human goods ordered by correct practical reason, not every actual inclination; rational nature and ultimately eternal law propose application/authority. | Establish other-regarding priority and its application to an indifferent agent without assuming the conclusion in “correct.” Proposed answer; authority unresolved. |
| Railton | Objective interests, then impartial consideration of affected interests; experiential correction and social arrangements can align individual and social rationality. | Equal weighting is substantive. Denial of universal instrumental reasons does not retract moral obligation. Open adequacy, not refuted and not automatically scope-incomplete. |
| Boyd | Human goods and sustaining mechanisms, causal reference and fallible empirical inquiry; needs/sympathy normally connect cognition and motivation. | Test whether the cluster and reference account warrant the selected verdict and what reasons are claimed for informed indifference. Contingency alone is not a contradiction. |
| Non-naturalist | Explicit independent normative truths and rational starting points; the existing Enoch third-factor account addresses epistemic access. | Primitive reasons need no infinite explanatory regress. Their content, comparative warrant and defeaters still matter; third-factor correlation does not supply the first-order norm. Open. |
| Expressivist | Plans coordinate deliberation and support forbidding/requiring, inference and correction without robust realist grounding. | Test coherent higher-order plans and conflict priority; do not demand acceptance of realism as the price of answering. The recorded Gibbard reply is a proposed guidance account, not a proof of universal reason. |

Two recognized goods plus feasible mutually exclusive acts leave priority open
in the existing typed conflict certificate. That does not establish that every
rival lacks a priority rule. The next comparison must use each proposed rule
under the same case description, including whether it offers pro-tanto or
all-things-considered guidance. Likewise a normative primitive is not defective
merely because it is primitive: compare discrimination, coherence, explanatory
reach and actual defeaters, without claiming those methodological virtues
mechanically entail truth.

### Rough-draft acceptance and connection reassessment

- Criterion: corrected to scope accountability; the stronger categorical-reason
  necessity remains disputed for the reasons above.
- Four-way answers: reused with Boyd as a second substantive naturalist. No new
  worldview bundle, score or machine answer-map cell is invented. The table in
  the existing comparison is the data consumed; its proposed Q-MORAL-AUTHORITY
  refinement is not misreported as a new Lean question registry.
- Non-entailment: already supplied by `HardCaseTyped.certificate` (fixed facts,
  same prohibitions with/without reasons), `HardCaseGoods` (shared nonconstant
  goods/damage), and Railton/Boyd ascription-consistency witnesses. These formal
  fragments do not show stronger theories admit arbitrary contrary verdicts.
- Positive bridge: rationale, explicit application premise and objection fixed;
  the application premise's derivation and independent warrant remain unfinished.
  The development implication is not delivered as philosophical progress by itself.
- End-to-end path: traced in existing answers above, with precisely located
  absent inference; no claim that source-answer availability establishes it.
- Root comparison: intended premise effect none. The target root-route leaf for
  connection is `STMT-GOODNESS-IS-ACTUALITY`, not the off-frontier seed. This work
  prevents confusing that leaf's ontological sense with practical authority; it
  does not discharge it or add an authority-to-God route. An actual connection
  requires a separately defended practical bridge and a reason that it bears on
  a named root inference. No such root inference is asserted here.

Overall provisional judgment: the evidence supports the restricted methodological
criterion and the missing-inference diagnosis. It underdetermines the stronger
necessity thesis and does not discriminate a metaphysical winner. This judgment
would change with a defended obligation/reason connection, a constitutive argument
that supplies other-regarding content without circularity, or a counterexample
to the restricted scope-accountability criterion. Independent semantic challenge
is required before the coordinator relies on this draft as reviewed support.

Reassessment requested: the rough draft's initial formal test is already covered;
the consequential continuation is substantive warrant for the rational-nature
application premise versus the obligation-without-instrumental-reason rival.
Do not close #563. The worker has not exhausted those arguments. The next worker
should fix one proposed argument's actual premises and harmful-deliberator case,
then encode its consequence and omission controls; source acquisition is not a
prerequisite for analyst formulations. This checkpoint preserves unfinished work
rather than claiming the assignment resolved.

Development evidence: shared preview clean HEAD
`078c37fd5d77f77c661b0d6ad8a8de5fe22c5d7c`, session
`research-master-20261110`, scratch `Scratch/moralauthority563/Edit.lean`.
Two full-content submissions returned no diagnostics: conditional application
SHA-256 `b90f92221e53f6ca8a4d2cbc080b7991f11ef87b1180d88d6946f926e68e3b26`,
then application plus omission witness
`5694a48ca4c8d3a421390ee34fdbbe7b755a8a4eb9689da853b053b0d5a5e581`.
Service elapsed times were 2.807s then 0.205s; this is warm-edit evidence,
not a controlled CLI speed comparison or final certification. Corpus lookup
returned the supplied preview revision and the seed-record hash
`1087b8014e53d6dd889d98781066b5af2b65e0ff758cf03d45948f4524751861`.
Retain for development; this run supplies no comparative CLI performance claim.
The implication and omission interpretations are stated above so the temporary
probe is not the only substantive record. No build imports were refreshed.

`corpus.py check` passed with existing warnings. Computed
`corpus.py frontier-diff --base origin/main`: 402 open root-reaching premises
(262 bare, 95 supported, 45 stated) unchanged; 288 verified support alternatives
unchanged; zero added; lowest expanded-route cost 16 unchanged; “no change.”
No Lean, statement, claim, argument or result record was changed. Final CI and
semantic challenge remain pending. Shared conventions resolved at sourceRevision
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
