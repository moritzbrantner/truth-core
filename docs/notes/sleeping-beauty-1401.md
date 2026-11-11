# Sleeping Beauty: probability space, evidence and update norm (#1401)

Analyst reconstruction, 2026-11-11; attribution deferred. This is the complete
proposed outcome for independent semantic challenge, not a reviewed victory for
a halfer or thirder. The frozen statements are in
[the batch](../../specs/sleeping-beauty-1401.toml); the substantive argument and
revision conditions below belong to the same outcome. Source leads in #1401
are navigation only: no new historical claim, passage or witness is introduced.

## Question and reuse

What change in Heads credence is justified by an awakening that was certain to
occur under either coin outcome? Fix the fair-coin experiment: one Heads Monday
awakening; two Tails awakenings, Monday and Tuesday, with memory erasure and
indistinguishable current awakening appearances. This finite reconstruction
supposes that those three centers exhaust the represented alternatives. It
does not model every possible protocol deviation, memory leakage or observer.
A world is the whole coin experiment. A center adds the awakening index.

Inventory used `related` and `dossier` on
`STMT-CORRECTION-CRITERION-EXACT-FACTORIZATION`, and `context` on
`CORRECTION-CRITERION-EXACT-FACTORIZATION`, with the #931 correction and #934
contrastive-update notes, dossiers and actual declarations. The existing
`CorrectionCriterion.characterization` is reused, not reproved. No existing
three-center measure/sampling vocabulary was found. #934 already distinguishes
normalization, likelihood discrimination, posterior preference and warrant;
its `Comparison` requires positive likelihoods at most one. The retained-slot
likelihoods below, 1/k and 1, respect that constraint. Treating an awakening
count k>1 as a likelihood would not. This work uses exact rational algebra
rather than duplicating the general Bayesian theorem or its normative claims.

The proposed application is to the epistemic warrant questions in #931/#934:
when does an identified observation procedure warrant applying a particular
update? That connection remains **UNBUILT**. No result here is a root route,
discharges a root premise, or settles worldview truth. Building the connection
would need a named actual inquiry, independently supported selection/likelihood
model, and a defensible reason to use that model for the agent's credence.
Merely importing a probability theorem does not supply that bridge. #1410's
divine veracity work depends on none of these declarations.

## Exact consequence within one measure

`Allocation` contains h,m,t≥0 with h+m+t=1. Let N be h=1/2, M be the positive-
denominator condition h+m>0 together with h/(h+m)=1/2, S be m=t, and P be t>0.
These formulas are claims about **one post-awakening centered measure**. A
Sunday experiment prior is not automatically that measure.

`incompatibility` derives:

1. N and M force t=0. From M, 2h=h+m; with N, m=1/2, and normalization gives t=0.
2. N,M,P are inconsistent. Removing P admits (1/2,1/2,0).
3. N,M,S are inconsistent. N,M force t=0 and m=1/2, contradicting S.
4. Under N and P, the Monday Heads conditional is strictly greater than 1/2.
   The denominator is 1−t, positive because h=1/2 and m≥0; 1−t<1.

`omissionControls` checks exact, nonvacuous assignments:

| Allocation | N | M | S | P | Heads given Monday |
|---|---|---|---|---|---|
| (1/3,1/3,1/3) | false | true | true | true | 1/2 |
| (1/2,1/4,1/4) | true | false | true | true | 2/3 |
| (1/2,1/2,0) | true | true | false | false | 1/2 |

Each premise omission of either inconsistent triple has a witness among these
rows; both rival positive rows assign every center positive mass. Minimality
is relative to the background normalization and specified formulas. It is not
minimality among all philosophical assumptions, and the zero-Tuesday row is
an algebraic control, not a persuasive full-support account of the protocol.
The finite twentieths-grid observation in #1401 is unnecessary as verification;
these universal algebraic proofs do not rely on that grid.

`appearanceBoundary` instantiates the actual existing exact-classifier theorem:
Heads Monday and Tails Monday have the same constant appearance but different
Heads truth values. No exact Prop-valued Heads classifier factors through that
report. The result does **not** show that the report has no probabilistic
relevance; a non-injective observation can have unequal likelihoods. It also
does not show that no richer evidence or fallible warrant is possible.

## Who selects, and what is conditioned on?

`Protocol` supplies 0<p<1 and a positive natural k: one Heads awakening, k Tails
awakenings. Two specified external procedures give distinct answers.

* Experiment selection: an external selector chooses an experiment according
  to its coin prior p and then chooses one of that experiment's genuine
  awakenings uniformly. Its Heads marginal remains p. For the fair k=2 case,
  this generates the halfer centered allocation (1/2,1/4,1/4).
* Retained-slot selection: the selector chooses an experiment with that same
  prior and independently chooses one of k potential awakening slots uniformly.
  It keeps the trial only if an awakening occurs in that slot. All Tails slots
  exist, while only one Heads slot does. Retention likelihoods are 1/k for Heads
  and 1 for Tails. Conditional Heads is (p/k)/(p/k+1−p).

`weightingAndWagers` proves that the latter is p/[p+k(1−p)], strictly between
zero and one, equal to p iff k=1, and strictly below p for k>1. The interpretation
of these algebraic weights as the described selector uses the explicitly
stipulated independent uniform slot distribution; there is no additional
formal stochastic process or empirical calibration theorem here. For fair
k=2 it gives uniform thirds. In large collections, pooling awakening
occurrences weights experiment types by their multiplicity. Saying “uniform
awakening” without specifying the pool or retention procedure leaves out just
this selection issue; for unequal priors it does not mean uniform weight over
the three abstract labels.

Both selectors are physically intelligible replacements for an ambiguous
sampling instruction. Beauty is not assumed to have been selected by either
one. She exists at every awakening in the original protocol. Moving from
these third-person selectors to her first-person evidence requires an epistemic
argument, not only normalization. The two selector descriptions identify a
concrete discriminating question: is her evidence appropriately evaluated as
a retained trial, or as locating herself inside an already selected experiment?

## Strongest positive rival accounts

The following are explicit analyst arguments. No historical author is claimed
to endorse every sentence.

**Halfer account.** The coin experiment was selected before any awakening. In
both coin worlds Beauty was certain to awaken; at least one awakening therefore
has likelihood one in each world. Ordinary conditionalization on that event
preserves her prior, giving N. To locate herself inside Tails, assign equal
weight to its indistinguishable occasions, giving S and the full-support halfer
row. This is an intelligible generative hierarchy, not arbitrary incoherence.
It respects experiment-level calibration and avoids treating her mere location
as an additional random draw from a pooled population.

Its price in one centered measure is abandoning M. A Monday announcement then
raises Heads to 2/3, since Monday has conditional probability 1 under Heads and
1/2 under Tails in this selected-center model. The fact that Monday occurs in
every experiment does not make “this selected awakening is Monday” certain.
That reply is valid within the stated selector. It owes a separate defense of
using that selector for a nonselected first-person occasion. A halfer retaining
both N and M must instead abandon positive Tuesday probability or depart from
ordinary conditioning in one fixed centered measure; the latter is a distinct
update framework, not a contradiction in probability theory. Such a framework
must specify how an announcement changes the space and why its rule is licensed.
No blanket refutation of every halfer follows from the triple theorem.

**Thirder account.** Each Tails awakening is evidentially indistinguishable, so
S is plausible. Given a Monday announcement, the two remaining histories each
contain exactly one Monday awakening and the original coin was fair; a
Monday-sensitive experimental observer who is present at Monday regardless of
the coin would retain odds 1:1. Applying that comparison to Beauty motivates M.
Together M and S uniquely suggest uniform thirds in this finite full-support
setup. Pooling actual awakening occurrences supplies a positive calibration
story; retained-slot selection gives an explicit equivalent likelihood model.
This explains how a known-to-occur event can still provide self-locating
information: the multiplicity of locations differs between worlds.

Its price is abandoning N and defending the transfer from a Monday-sensitive
observer or occurrence pool to Beauty's own current evidence. Certainty of
some awakening does not by itself refute this account, because that is a
coarser event than being the particular centered observer under a selector.
Conversely, observational indistinguishability alone never proves equal
probability: equally looking tickets can have different prior weights.
To warrant M one must justify why the Monday information leaves the coin odds
unchanged for **this** agent. Using fairness to equate centered masses already
assumes the disputed comparison. To warrant S one needs temporal symmetry or
a selection/indifference norm in addition to identical appearances. In the
stated reset protocol neither Tails day has a distinguishing report, which
supports symmetry within a specified model, but that does not settle how total
Tails mass compares with Heads mass. Both live accounts can endorse S.

The rival disagreement therefore descends to the transport of experiment
priors into a current centered space, and to whether the evidence includes a
multiplicity-sensitive selection event. Both use Bayesian algebra after fixing
that interface. Repeating “Bayes” or “no new uncentered fact” cannot identify
the disputed interface. A model that separately tracks experiment credence and
awakening-based decision weights may retain both as different quantities; it
must not report them as a single measure satisfying N,M,S simultaneously.

## Wagers: settlement is part of the argument

The new gain functions evaluate a **Sunday fixed policy**, with linear additive
utility and the same rational price c at every eligible occasion. An external
accountant computes expected net gain under the experiment prior p.

* Once per experiment: charge c and pay one iff Heads, exactly once. Expected
  net gain is p−c; the unique zero-gain price is p.
* Once per awakening: charge c at each awakening and pay one at the unique
  Heads awakening, hence k charges and no payout under Tails. Expected net gain
  is p−c[p+k(1−p)]; the unique zero-gain price is p/[p+k(1−p)].

For fair k=2 these prices are 1/2 and 1/3. A bettor can rationally distinguish
the two contracts under the same Sunday coin credence. The second balance
condition counts more losses under Tails; it does not force a change in coin
credence unless a further norm identifies current credence with that particular
policy's fair ticket price. Likewise, charging once per experiment while
paying for each awakening, nonlinear utility, shared bankrolls, decisions by
only one awakening, or conditioning a current decision on future/previous
choices changes the decision problem. None is encoded by these gains.

Thus the wager result is neither a Dutch-book construction nor an immunity
result. A stronger Dutch-book argument needs explicit admissible transactions,
information at each offer, diachronic update/acceptance rules, settlement and
utility aggregation, with a proof of the claimed guaranteed loss. A guaranteed
loss under a specified policy can challenge that **policy**, but identifying
its source with a unique rational credence remains a further step. Mere ticket
counting cannot dismiss either rival epistemology.

## Proposed overall provisional assessment

As of this evidence revision, the mathematical diagnosis is decisive **within
the specified single-measure framework**: N,M,S cannot coexist; neither the
full-support halfer nor thirder allocation is probabilistically incoherent.
The normative conclusion is currently **underdetermined**. There is positive
reason for the halfer's preservation of experiment prior when the evidence is
just existence of an awakening, and positive reason for the thirder's
multiplicity weighting when the evidence has the retained-slot/pooling
selection semantics. These reasons share the fair-coin/reset setup and
ordinary conditional algebra, so they are not independent confirmations of a
single measure. Their disagreement is the applicability of the evidence model.
Neither normalization, the exact-classifier obstruction, nor the settlement
calculation resolves it. This is a reasoned suspension on unique rational
credence, not a declaration that every allocation is equally justified.

The strongest standing halfer objection is that no pool-selecting mechanism
occurs in the stipulated experiment. The strongest standing thirder objection
is that the halfer excludes multiplicity from first-person evidence without an
independently warranted reason, despite occurrence calibration and the Monday
comparison. Their positive replacement accounts and exact costs are above.
Other update frameworks, decision-theoretic norms and observer-reference
classes have not been exhaustively excluded. No metaphysical winner, F6 change,
formal defeat of a rival or Catholicism-root establishment follows.

Revision conditions and next tests:

1. A justified account of first-person evidence selecting one protocol would
   discriminate the rivals. Specify the sample space, observation map,
   retention event and reference class; derive the likelihoods rather than
   importing the desired answer. Test it on duplicated observers, unequal p,
   and variable k, including k=1. The current algebra supplies sensitivity tests.
2. For the Monday argument, compare an observer placed at Monday by construction
   with one informed that a selected awakening is Monday. A proof that the same
   first-person evidence norm governs both would support M; a warranted
   distinction would weaken that transfer. Their distributions already differ
   in the two explicit selector stories, so indistinguishability alone is
   insufficient.
3. For a betting argument, formalize one complete information/policy/settlement
   game and determine whether the demanded coherence is experiment accuracy,
   occurrence accuracy or diachronic utility. These are coexisting standards
   until an argument connects them. Changing settlement alone is already known
   to change the fair price.

The bounded mathematical assignment has four proved heads; the affected local
Comparator/NanoDa and binding gates passed, with delivered-head CI still required.
The broader epistemic branch remains open for coordinator reassessment: a
consequential next assignment is to defend or reject one transport principle
under those controls, rather than generate more normalized allocations. No
owner choice between philosophical winners is required.

## Claim/type self-sweep and development evidence

The four proposition heads exactly separate universal incompatible bundles,
explicit omission/full-support witnesses, conditional sampling/settlement
algebra, and a specialized exact-appearance obstruction. Definitions specify
every quantified variable, nonzero denominator and probability boundary.
Rational finite weights are a restricted exact arithmetic model; extension to
real measures or arbitrary observer populations is not claimed. No primitive
rationality predicate is smuggled in as a proved norm. No sources, claims,
legacy allowlist additions or shared #931/#934 definitions are changed.

The shared service was used with endpoint `http://127.0.0.1:8879`, preview
`e02bd650c2f31160dd1f965b439b1c185cdb421c`, session `continuation-1111`, path
`Scratch/beauty1401/Edit.lean`, and its shared lease via `agent_lean.py`.
Owned vocabulary and Solution were inlined into a temporary submission because
new canonical modules do not exist in the clean preview. This is development
evidence for that submitted content, not a build of the worker's imports.
Two recovered prior edits exposed genuine tactic/import errors; corrected full
content returned no errors in 2.81 seconds client time (2.70 seconds service),
and the retained-slot extension returned only an unused-tactic warning in
3.07 seconds (2.96 service). The unused tactic was removed before canonical
build. A service dossier query also returned a revision/input-bound result.
The focused canonical Lake build passed against the separate files. A
representative CLI elaboration of the canonical Solution completed without
diagnostics in 2.95 seconds, compared with the roughly 2.8–3.1 second service
submissions above. These single requests showed no clear latency advantage;
the service did provide persistent edit/version and input binding evidence.
No general throughput advantage over CLI is inferred.
Recommendation: retain for repeated proof goals/edits with built shared imports;
revise workflow guidance to mention explicit inlining for new owned modules,
or let the coordinator refresh preview imports when justified. The shared
session did not certify the final revision; final delivered-head CI retains
build, binding, axiom, Comparator and NanoDa coverage.

## Reflection continuation: proposed complete outcome after #1411

This continuation received its own independent semantic challenge and was
accepted, including the full qualified assessment below. The reviewed evidence
hashes were note `32a85e51`, vocabulary `7173b472`, Solution `27c3323e`, and
spec `e69db6d5`; subsequent edits update work status only. The earlier #1411
review was reused only for its unchanged checkpoint. The new frozen heads live
in [the continuation batch](../../specs/sleeping-beauty-reflection-1401.toml)
and [Reflection vocabulary](../../TruthCore/Epistemology/SleepingBeauty1401/Reflection.lean).
No claim of a built root/warrant connection is added.

### Inventory and exact question

The continuation inspected reflection, perfect recall, amnesia, forgetting,
non-nested evidence and conditional-expectation terminology across existing
Lean, statements, definitions, attempts and notes. `ReflectiveCoherence` is
about truth-directed worldview duties, not probabilistic future deference;
the Goldman forgotten-evidence note concerns preservation of warrant, not
this conditional-probability theorem. Neither is repurposed as a reflection
certificate. The existing `EpistemicAccuracy.regret` theorem is actually used
for the designated-Monday score, with its context/dossier and interpretation
boundary inspected. No duplicate general accuracy library is introduced.

The question is whether knowing one's future Heads credence gives a reason to
defer to it, and whether known memory erasure removes that reason. The strongest
ordinary reflection argument treats the future credence as a correctly
conditioned estimate on evidence that preserves current information, for the
same target, population and probability measure. In that setting the usual
conditional-averaging argument motivates deference. It does not follow merely
from the existence of a future opinion. The new results are concrete controls;
they are NOT a general formal tower-property or reflection theorem.

### Relevant loss, irrelevant loss, and what the controls establish

`amnesiaControl` fixes the SAME fair two-world coin throughout. Initially the
agent sees the coin world; a Heads report gives conditional 1 and a Tails report
conditional 0. Afterwards the report is erased, so either world yields the
same report and conditional 1/2. The agent can know in advance that this will
be the future credence. Conditioning now on both current report and the known
future one-half report still gives 1 or 0. Every event used has positive mass.
Thus the unrestricted prescription “if I know I will later assign r, assign r
now” fails even when both credences are actual report-conditioned probabilities.
The future report cannot reconstruct the initial one. The example identifies
a genuine reason against unconditional future deference: the future self will
lack reliable target-relevant information already available now.

`irrelevantLossControl` adds an independent fair private bit, making four equal
atoms. Knowing either bit value leaves coin probability 1/2. Erasing the bit
leaves it 1/2 as well, despite failure of report reconstruction. Thus structural
information loss is neither an automatic update rule nor a sufficient reason
for a change in this target credence. A target-sensitive account must ask what
was lost, its relation to the target, and which probability model supports that
relation. This refines the amnesia objection rather than declaring it generally
irrelevant. The pointwise `Retains` factorization is an ideal extensional
information relation; it does not encode personal memory, reliable access to
reconstruction, or epistemic obligation.

For Beauty, Sunday does not contain a revealed coin outcome subsequently
forgotten. At the first actual Monday awakening she has not erased an earlier
awakening's coin evidence. Consequently the relevant-loss model is not a direct
proof that her first-Monday credence may differ from her Sunday credence.
However, this does NOT prove perfect recall or nested first-person information:
on Sunday she can identify her next awakening as the first Monday one; later
she cannot identify her current awakening as first Monday rather than Tuesday.
Memory of the protocol does not restore that current-location relation.
Whether this is relevant information loss for an uncentered target, and how to
represent it in a common temporal sample space, is precisely a disputed bridge.
A blanket assertion of either “no information lost” or “amnesia, therefore
reflection inapplicable” skips it.

`firstMondayCalibration` makes the external-cohort side exact. Select exactly
one first-Monday assessment from each fair coin experiment. If the reported
credence is the same r in both worlds, conditioning on that report still gives
1/2. A constant 1/3 forecast is not calibrated within THAT cohort. The reduced
coin-only Sunday and first-Monday reports are both constant and retain each
other, so information loss is not represented in that reduced model. This is
a control on a proposed modeling claim, not a theorem that the reduced model
contains all Beauty's centered information. Imposing it as her rationality norm
would assume the contested transport. Conversely, a thirder accepting ordinary
first-Monday calibration as an overriding norm for her own report would face
this exact discrepancy; “there are two Tails awakenings” alone does not repair
that cohort's conditional frequency.

### A positive rival norm without bets

There is a substantive positive epistemic argument for the thirder policy:
evaluate the expected SUM of epistemic inaccuracies of every actual awakening
credence. Each actual erroneous assessment contributes a squared-error cost;
all awakenings have the same per-token scoring rule, with no money, pleasure,
wealth or practical reward. Restrict to one common policy r because the agent
lacks reliable day information. In the fair one-H/two-T protocol the expected
sum is

`tokenRisk(r) = (1/2)(1-r)^2 + r^2`.

`cohortAccuracy` proves that 1/3 uniquely minimizes it, with regret
`(3/2)(r−1/3)^2`. Choosing 1/2 instead adds 1/24 expected total error. The norm's
positive reason is preventing more inaccurate credence occurrences across the
occasions the agent will actually undergo. This survives the objection that
thirder betting prices might merely reflect financial settlement: this new
criterion concerns epistemic error itself.

There is an equally explicit positive halfer criterion. Evaluate one designated
Monday assessment per fair experiment, or average the identical-r token errors
SEPARATELY within each realized experiment before taking the coin expectation.
Either yields

`mondayRisk(r) = (1/2)(1-r)^2 + (1/2)r^2`.

Its unique optimum is 1/2, with regret `(r−1/2)^2`; 1/3 adds 1/36 expected error.
The positive reason is calibration to the fair experiment-level target without
letting repeated occasions in one outcome give that experiment greater weight.
The averaging interpretation here is justified by the explicit constant-policy
restriction; it is not asserted for arbitrary varying token policies. It also
is not the same as dividing expected total error by expected token count,
which just multiplies `tokenRisk` by a fixed positive factor and keeps 1/3.

The result proves no common minimizer for these two selected objectives. In the
Heads state 1/2 has smaller squared error; in the Tails state 1/3 does. There is
therefore no statewise dominance argument between these two coherent policies.
The general coherence-dominance theorem for inconsistent complementary
credences cannot choose one: both r and 1−r form coherent pairs. These are two
competing epistemic aggregations, not the same score with an algebra error.
The choice of squared error is explicit; no theorem about every possible proper
scoring rule is claimed.

The standing objection to the token norm is that an ex ante policy optimum
across multiple future assessment occasions does not automatically fix the
rational truth-directed credence at this particular occasion. It must justify
additivity across tokens and why duplication of relevant episodes changes the
required credence while ordinary duplication of score records does not. The
standing objection to experiment averaging is that equalizing experiments
underweights the actual additional Tails episodes at which the subject may be
wrong. It must justify the experiment as the epistemic unit and the transport
of that unit to a current self-location. Neither objection exhibits a conflict
with an accepted floor commitment or with the rival's own stated objective.
Neither norm is dismissed merely because its preferred unit is unusual.

### Common controls and remaining disagreement

The positive norms agree on several discriminating cases; they are not blanket
recipes to move every prior or ignore every announced day.

* With one awakening per outcome, the two populations coincide; the existing
  general p,k certificate verifies that their probability weights coincide.
* If a reliable report distinguishes Monday from Tuesday, Monday can use 1/2
  and Tuesday 0. `recallControl` proves day-sensitive total error 1/4, strictly
  below the best constant policy's 1/3. Its exact regret is
  `(mon−1/2)^2 + (1/2)tue^2`; restricting mon=tue recovers `tokenRisk`.
  Thus the total-token criterion values retaining a relevant day distinction;
  it does not prescribe thirds regardless of available information. The
  experiment-level first-Monday criterion also favors 1/2 at that designated
  occasion. Tuesday certainty is consistent with either truth-directed account.
* Losing an independent private bit leaves the fair target credence unchanged.
  The new four-state control proves this rather than assuming all information
  loss is target-relevant.
* Losing an actual outcome report changes the appropriate report conditional;
  both positive accounts can reject unrestricted deference to the less-informed
  future self. A normative bridge is still needed to say which future report
  conditional is relevant to the actual agent.

Changing the information regime changes the assessed policy class. The
retained-day comparison is a different regime from announcing Monday to an
already day-ignorant agent and conditioning her existing centered measure.
It therefore does not refute the halfer's 2/3 Monday announcement posterior by
silently treating two different evidence/sampling interfaces as identical.
It identifies the interface a proposed bridge would have to equate.

### Proposed revised provisional assessment and reassessment

The unique-rational-credence judgment remains underdetermined, but the reason
is now sharper. Unrestricted reflection is refuted by an explicit relevant-loss
control. Structural memory loss by itself does not settle a particular target,
as shown by the independent-bit control. First-Monday calibration supplies real
pressure on a constant thirder forecast IF that designated cohort is the
appropriate epistemic unit; total-token epistemic accuracy supplies a positive
countervailing policy reason for thirds that does not rely on betting payoff.
Both norms survive the common controls above under their explicit objectives.
They disagree about the unit and temporal transport of epistemic assessment,
which the mathematical certificates do not make obligatory.

The new positive support for thirds is conditional on additive total-token
accuracy, not support for its universal normative authority. The new pressure
from reflection is conditional on retained target-relevant information in a
shared population, not a proof of halfer superiority. Shared dependencies are
the fair protocol, target stability, same squared-error rule and reliable
report interpretation; the two accuracy computations are not independent
witnesses to a single norm. No norm, rival defeat, root connection or closure
is upgraded by this assessment. No historical attribution has been added.

A concrete next discriminating assignment is now normative rather than more
normalization: compare total versus per-experiment epistemic aggregation under
a duplication intervention that keeps the agent's available report, causal
coin evidence and target fixed. Specify whether the new objects are actual
conscious assessment episodes or duplicate administrative score entries, and
whether one policy must govern all episodes. Defend why either intervention
may or may not alter epistemic reason. Also test a reliable positional marker
that preserves knowledge that the current awakening is the next one predicted
on Sunday, separately from memory of the coin protocol. A defended account of
that temporal-index relation could warrant or defeat the first-Monday
reflection bridge. Merely defining a prior-preserving selected-self kernel,
counting all copies, or calling one regime “the real evidence” would prejudge
it.

This is a branch reassessment point: the selected mathematical controls are
resolved; further inferential progress requires defending the rival epistemic
unit/transport norm against this concrete duplication/index test. No unavailable
source or owner choice is alleged. The coordinator may allocate that narrower
normative question rather than repeat the existing algebra. The complete
outcome is persisted and independently challenged. Canonical focused build,
preview diagnostics, five-result binding and all five Comparator/NanoDa checks
have passed; delivered-head CI remains required for the new continuation results.
