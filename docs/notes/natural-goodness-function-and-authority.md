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
| Rational regulation | The formal reading licenses inclusion for human natural inclinations when rational regulation is supplied; it records only the sufficient direction. Correctness and authority remain open. The stronger source qualification above is separate from this formal direction. |
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

## Positive agency argument continuation (#563)

Continuation of PR #1389, following independent review of its base audit.
The review's localized repair is incorporated above: the formal inclination
reading has only a sufficient direction. The following new findings require
independent challenge; the base audit's review does not cover them.

### Fixing the proposed argument and its meanings

This is an **analyst reconstruction**, not an attribution to Kant or a claim
that all natural-law theories accept its premises. The selected agency argument
is: (1) deliberation toward any end requires some capacity to choose and act;
(2) that indispensable capacity supplies the deliberator a reason to preserve
it; (3) the reason-giving feature is agency, shared with other humans, rather
than the bare identity of its possessor; (4) damage to another's agency therefore
gives this deliberator a reason for restraint. Its strongest attraction is that
neither a voluntary practice nor an already benevolent desire selects the
standard: the wrongdoer still exercises the capacity invoked in (1).

These are separate steps. (1) is a necessary-condition proposal about effective
agency; it does not say that every deliberator must maximize future agency,
never sacrifice life, or protect everyone's agency. (2) is a normative bridge,
not the descriptive claim that means are necessary to an end. A reason to retain
capacity for an intended action can be instrumental and temporary. A person
can coherently accept loss of future agency to save someone else; that does
not refute all pro-tanto self-preservation reasons. The further thesis that
agency has noninstrumental value needs its own warrant.

Even granting (2), (3) is ambiguous. Consistency under exchanging *both* the
reason holder and beneficiary permits the relational rule “each has reason to
protect their own agency.” Holding the beneficiary fixed while exchanging the
reason holder is stronger. The claim that a shared natural property removes
all such relational dependence does not follow from common humanity alone.
Objective good **for** someone retains that person's coordinate. Conversely,
this observation does not establish that only relational reasons exist.

Here “agency” means capacity to deliberate and carry out chosen actions;
“protect” concerns retaining that capacity. Their positive value, the causal
role of a particular injury, and the transition from capacity to a reason are
OPEN interpretation/application obligations. The formal test below has a
primitive reason matrix; it does not define agency or rational excellence.
It uses the existing two humans, not a new ontology of worlds or persons.
There is no predicate whose definition makes rationality moral agreement.

The proposed conclusion is an **other-regarding pro-tanto reason**. That is
separate from obligation, an instrumental reason, motivation, recognition and
a decisive reason. No result here establishes independence across changing
preferences. A pro-tanto reason can remain when outweighed; excluding all
outweighing reasons needs a priority premise. The existing `Verdict.reasonAgainst`
is documented as categorical and action-indexed. The matrix does not silently
identify that predicate with this weaker protection-reason relation.

### Exact test and what the witnesses establish

New spec: `specs/moral-agency-neutrality.toml`; vocabulary:
`TruthCore.Ethics.AgencyNeutrality.Controls`; frozen Challenge and real Solution:
`TruthCore/Results/Ethics/AgencyNeutrality/`. Definition record is linked by the
generated argument. The Solution wrapper syntactically states that exact
`Controls` declaration. Local development elaboration succeeds and `#print
axioms` reports no axioms; final binding/Comparator/NanoDa certification remains
pending. Registration alone confers no new verified status.

For a supplied matrix `R p q`, read the entry as a pro-tanto reason of p to
protect q's agency in the stipulated case. The structural controls are:

- Diagonal identity entries are reflexive and preserved by every simultaneous
  relabeling; the offender/victim entry is false. This demonstrates why joint
  relabeling alone cannot justify transferring a reason across agents.
- Given `∀ p, R p p`, the premise `∀ p q, R q q → R p q` is equivalent to
  `∀ p q, R p q`. Thus this proposed transfer premise provides no independent
  support if its only defense repeats the target's universality. Equivalence
  alone does **not** discredit an independently defended premise.
- The full matrix witnesses the self-reason and transfer premises jointly.
  The diagonal matrix retains all self-reasons while lacking the offender's
  reason for the victim. The empty matrix retains the transfer rule vacuously
  while lacking that reason. Both premises matter to this conditional proof;
  neither witness is claimed to satisfy a complete philosophical theory.
- Private payoffs 3 versus 1 and equal sums 3 + (-10) versus 1 + 0 reverse
  the order. Only these integer inequalities are encoded in the payoff cell;
  it does not encode a complete decision procedure or actual human psychology.

The matrices are **structural surrogates**, not metaphysical countermodels of
rational natural law. R is supplied independently; the diagonal interpretation
is a witness, not a definition of what reasons really are. No claim of
exhaustive moral alternatives, semantic completeness or actual rational
permissibility follows. A natural-law theorist may reject the diagonal model
on independently defended substantive grounds. That rejection must identify
the ground; merely renaming the full matrix “correct reason” adds no defense.

### Harmful but effective deliberation on the same case

Use the killing case already represented by `HardCases`: deliberate killing
of an innocent nonthreatening victim, offender indifference, private benefit
and absence of punishment. Add explicit **scenario assumptions**, not facts
inferred from that certificate: abstention is feasible; both humans retain
agency absent the killing; killing destroys the victim's future agency;
the offender knows the injury, can select effective means, reasons consistently
about the stipulated ends, and anticipates no sanction, future exchange loss
or hidden private cost in this choice. The original finite certificate does
not model these epistemic/deliberative capacities or guarantee their joint
metaphysical possibility. Its `Facts` fields remain the factual starting point.

The numerical discriminator sets kill/abstain payoffs for the offender to 3/1
and for the victim to -10/0. These are stipulated comparable interests for the
illustration, not measurements or a historical author's calculus. Private
maximization selects killing; equal-sum comparison selects abstention. The
wrongdoer recognizes the victim's injury and does not make a calculation error.
This removes the easy replies that the offender merely misunderstands injury
or chooses ineffective means. It leaves open whether this informed, coherent
agent is rational in a thicker normative sense. Calling that thicker sense
correct requires defending its content, not changing the stipulated arithmetic.

A universal policy of benefiting oneself at outsiders' expense can preserve
indexical consistency. If everyone adopts it, the offender may face risks;
that supplies an instrumental objection in cases with those risks. It supplies
no contradiction in the present no-retaliation choice. “Would you accept being
the victim?” also distinguishes two questions: disliking that position does
not entail refusing advantage in the actual position; a requirement to accept
only rules justifiable from every position is a substantive reciprocity norm.
This test does not address every formulation of universal law, duties against
using persons merely as means, or every constitutive theory of agency.

### Strong replies and their remaining premises

The strongest natural-law reply need not maximize aggregate benefit. It can
hold that justice and common good are constitutive excellences of rational
social animals, and that deliberate injury is contrary to an agent's own
rational flourishing even when privately profitable. This supplies positive
content absent from bare means-end consistency. It must defend why the relevant
human good includes just relations, why this act violates them, and how that
good gives this wrongdoer a pro-tanto reason. A further priority premise is
needed for prohibition or decisive restraint. The existing function reading
provides only necessary excellence conditions for a specified function; the
first precept does not establish these application claims.

Three candidate defenses of the missing premise were tested conceptually:
common natural features leave relational good-for intact; consistency under
joint relabeling leaves the diagonal model intact; and instrumental reciprocity
requires dependence, vulnerability or future interaction excluded from this
choice. None supplies the specified noninstrumental transfer. Stronger
reciprocity as equal justificatory standing can supply it, but then its warrant
rests on that normative standing and its application. It is legitimate to retain
that as an explicit primitive or defended premise. It is not a deduction from
instrumental coherence, and the encoded equivalence explains why the bare
transfer formulation should not be counted as new independent evidence.

Compare positive alternatives on these same injury/knowledge/payoff assumptions:

| Account | Positive resources on this choice | What remains open |
|---|---|---|
| Rational natural law | Human flourishing includes rational social excellence/justice; victim agency is a human good. | Defend that constitutive account and its application to this offender; establish the pro-tanto bridge and any priority. Private profit alone does not refute it. |
| Railton | Objective interests can correct current desires; the impartial standpoint counts both affected persons. Under the illustrative equal-sum assumption it favors abstention. | Do not turn this numerical illustration into Railton's complete decision rule. His recorded obligation/reason distinction permits moral obligation without a universally present instrumental reason. An indifferent informed offender therefore does not refute his advertised account. |
| Boyd | Human needs and social mechanisms can fix a goodness standard despite indifference. | No verdict on this exact case follows merely from the name of a goods cluster. Specify the relevant goods, mechanisms and ordering. Their normal motivational connection need not hold without exception. |
| Primitive normative realism | An independently warranted reason against destroying another's agency can govern the offender despite private gain. | Content, strength, applicability and access require defense. The Enoch access reply does not itself provide this first-order reason. Being primitive is not an inconsistency. |
| Planning alternative | A coherent plan can forbid the injury and guide deliberation while recognizing the gain; shared planning can criticize contrary plans. | Coherence alone does not select the protective plan. Defend the relevant commitment and conflict priority within the account's advertised scope. This does not force a realist truthmaker or universal motivational thesis on it. |

### Reassessment, acceptance and reopening

The selected **bare constitutive self-concern plus joint-universalization
argument** is resolved conditionally: its purported other-regarding step is
missing; strengthening relabeling to beneficiary-fixed transfer supplies the
conclusion but does not independently defend it. This is an inferential diagnosis,
not a refutation of natural law, Kantian ethics or categorical reasons. The
remaining philosophical question has shifted to substantive justice/equal
justificatory standing, rather than a further consequence of identity symmetry.
The three defenses just tested repeat that same precise obstacle when restricted
to their current premises. Repeating the original thin countermodel would add
nothing. A materially different next test requires a specified independent
argument for constitutive justice or equal standing and its actual premises;
this note supplies the target and objection for coordinator reassessment.

Overall provisional judgment: these tests favor the diagnosis that instrumental
coherence and common human agency, as specified, leave other-regarding content
unsettled. They do not favor a metaphysical winner. A substantive defense of
justice as rational flourishing, equal standing, or a first-order normative
reason could change that judgment. Independent challenge must examine this
new synthesis and the structural-surrogate boundary before it is relied on.

Acceptance delta: the original rules-without-bindingness evidence remains reused;
the positive argument now has explicit independent steps, strongest replies,
harmful-deliberator comparison, and consequence/omission/joint controls. Actual
human rationality, the normative bridges, action-specific priority and final
certification remain open. The original criterion and answer-map analysis stand
with the reviewed sufficient-direction repair. No root inference is added:
#369/#371/#373 still require the practical bridge and a warranted connection to
`STMT-GOODNESS-IS-ACTUALITY`. This is conditional structural progress, not root
closure or completion of the wider #563 investigation.

Service evidence: the supplied exact preview binding was rejected with
`agent_lean: preview HEAD differs from --expect-head; obtain the current handoff`.
No preview/session was changed or restarted. Corpus lookup reported clean HEAD
`3aaf6c4fdb8bd9ed781ee7cb57811d5d81f84964` and first-precept record SHA-256
`76ad39f1aa4a56b2cf018b03abfe2ceafc4b0cdc525bbba88ccabd8feff0f39b`.
Repeated full-content service edits could not responsibly proceed on the stale
binding. CLI probes and canonical vocabulary/Solution elaboration instead used
`worker_env.py -- lean` and explicit `LEAN_PATH` over warm compiled imports,
with a temporary symlink overlay for the new module outputs. Lean resolves the
module package root from the first path, so simply listing local and warm roots
in opposite orders failed for one of the imports; the overlay resolved this
without editing the warm checkout. Retain the service protocol, revise stale
handoff bindings; no controlled latency comparison is available from this run.

Computed delivered-change comparison against main `a55e209f6`:
```
open premises reaching the root: 402 (262 bare, 95 supported, 45 stated) -> 402 (262 bare, 95 supported, 45 stated)
distinct verified support alternatives: 288 -> 288
verified support alternatives added: 0
no change
```
Lowest expanded-route diagnostic remains 16. Claim/type self-sweep: no historical
claim added; the one new statement matches the Controls wrapper, quantifies
only the two supplied persons/matrices, and labels the missing real-case
interpretation explicitly. No statement identifies pro-tanto protection with
obligation, instrumental gain, categorical action reason or decisive priority.
The new dossier links the exact definition and the existing attempt retains
failed approaches and revision conditions. Existing source records are preserved.

Final local gate disposition for the new result: vocabulary and Solution
compiled against warm outputs; frozen Challenge compiled with its expected
`sorry` warning. `bind-check --result c2309982-932d-453a-8513-1aad8761bec4`
reported `1 bound, 0 pinned, 0 mismatch`. Comparator/NanoDa remains unverified:
```
Building TruthCore.Results.Ethics.AgencyNeutrality.Challenge
comparator error: sandboxed lake build TruthCore.Results.Ethics.AgencyNeutrality.Challenge exited with exit status: 1
error: build failed
```
No unsandboxed retry was made. Delivered-head CI must certify the result.
Vocabulary SHA-256 `a3fe96916c07fc7ce5d7cd438fc3a7de654d009f567dfdc64239ae77e1d2a259`;
Solution SHA-256 `20451ec210867039cfa5928c661da727ed850b01ceaa91c03d2ead25eec6ebc6`.
Generator rerun wrote zero files and corpus check passed. The warm-output
symlink setup is disposable readiness, not final certification. The direct
CLI check used the supplied toolchain/cache setup; no external dependency was
added to the manifest or source. `lake env` materialized existing pinned
packages locally before the focused checks.
