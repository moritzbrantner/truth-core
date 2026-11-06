# Fallible correction with an implementable mistake bound (#931)

Analyst reconstruction, attribution deferred, 2026-11-06. No historical claim
about Carneades.org or an author's intentions is made. This investigates how a
method can improve inquiry without assuming exact classification or treating
coherence, approval or an attractive result as truth.

## The positive result

There is a finite, executable updating method with a proved guarantee on
**actual mistakes**, allowing both mistaken experts and misleading feedback.
It does not need to identify the best expert or the false feedback labels.
For example, over any finite horizon, if two experts include one with at most
two actual mistakes and feedback has at most one false label, this method
makes at most ten actual mistakes. The horizon may be much longer than ten.
The expert need not be perfect and the labels need not be infallible. Neither
condition is established simply by looking at the learner's apparent success.

This is something true about an available method, not a claim that the actual
world satisfies an invented reliability premise. The theorem covers **all**
advice, feedback and truth streams in its explicit binary setting. Its proof
explains the guarantee through changing vote weights; the conclusion is not
already supplied as an opaque bridge premise. The resulting positive reason
for using this method is restricted: independently supported low-error experts
and feedback make it a way to control accumulated error without requiring a
truth oracle. The evidence needed for that application is a separate question,
addressed below rather than hidden in a predicate named `Justified`.

## What the method actually does

Fix N experts, each giving a binary answer before each round's feedback arrives.
A round can ask a different question; neither stationary truth nor independent
random observations are assumed. Start each weight at 1. Predict the weighted
majority, breaking an exact tie toward true. After the feedback label arrives,
halve the weight of every expert disagreeing with it; retain the others.
The next round uses these revised weights. All weights are positive rationals,
so a finite pool requires only finite exact arithmetic. This is a mathematical
executable, not an efficient production implementation or machine learning
service. Experts can be people, explicit rules or instruments; their title
confers no reliability. Duplicating advisers changes the pool and its guarantee.

`weights advice feedback n` depends only on earlier feedback. The current
prediction uses current advice. The separate `truth` stream is used only to
evaluate mistakes, never to make a prediction or update. The particular expert
used to state a guarantee is an arbitrary `i : Fin N`, so that application is
nonempty. Nothing requires the algorithm to recognize that expert as good.

For the first n rounds write:

- M: learner disagreements with feedback;
- m_i: expert i disagreements with feedback;
- L: learner disagreements with actual truth;
- e_i: expert i disagreements with actual truth;
- K: disagreements between feedback and actual truth.

A **mistake** is a mismatch between the predicted binary answer and the supplied
actual answer to that same question. It is not disagreement with the group,
incoherence among beliefs or dissatisfaction with a practical outcome.

The Lean proof establishes these facts from the update rule:

1. Expert i's weight is exactly `(1/2)^m_i`.
2. Total weight never increases. Whenever the learner disagrees with feedback,
   at least half the previous weight supported its mistaken prediction, so
   halving that weight leaves at most three quarters of the total.
3. Consequently `(1/2)^m_i ≤ N*(3/4)^M` for **every** expert.
4. Pointwise disagreement gives `L ≤ M+K` and `m_i ≤ e_i+K`.
5. If `K≤k`, monotonicity of powers between zero and one gives
   `(1/2)^(e_i+k) ≤ N*(3/4)^(L-k)`, with natural subtraction truncated at zero.

This is the exact power form of the usual weighted-majority mistake guarantee;
no logarithm, distribution, perfect hypothesis or stationarity is assumed.
For N=2, e_i≤2 and k=1, L≥11 would force
`1/8 ≤ 2*(3/4)^10`, which is false. Thus L≤10. The numerical corollary is
checked, not an extrapolation from a few successful trials. The count can be
uninformative when all experts are poor or k is large. A bound at horizon n
does not establish future bounds; uniform future control requires the
antecedents to hold over those horizons too.

## Concrete correction and misleading evidence

The same two experts constantly answer false and true. Weights initially are
(1,1), so the tie rule initially answers true. Feedback false changes weights
to (1,1/2), and the next prediction is false. A subsequent true label changes
them to (1/2,1/2), restoring a true prediction. With actual truth always true,
this three-round trace has one misleading label, one learner mistake and an
expert with no actual mistakes. Its recovery does not make the false label true.

If labels instead remain false, the learner answers false on **every** round
after the first. When actual truth is false this corrects the initial mistake:
in any n+1 rounds it makes exactly one mistake, while an obstinate always-true
predictor makes n+1. This is a strict cumulative improvement after the first
round. With identical advice and labels but actual truth true, the very same
update makes an actual mistake on each subsequent round. At each time each
account can hold a single consistent binary belief. They cannot both be accurate under the fixed truth
interpretation. This is a jointly inhabited binary control, not an inference
from failed proof search or an empty background.

For the three-round trace, the report projection forgets which of the two
truth states obtains.
The existing `CorrectionCriterion.characterization` therefore rules out an
exact classifier for that truth using those reports alone. We import it and
apply its fiber constraint; we do not reimplement the generic no-go theorem.
This restricts unrestricted report-only access, not all fallible warrant. The
learner's prediction and the reports agree in the misleading case, so mere
coherence or convergence to consensus cannot rescue actual accuracy.

## When there is a reason to revise

Here is the proposed restricted warrant bridge, stated as a philosophical
argument rather than a proved normative definition:

> Independently supported indications that a method controls errors relevant
> to one's factual question, together with a checked connection from those
> indications to that control, supply a defeasible epistemic reason to use or
> revise toward that method, proportionate to that support and open to defeat.

Why accept it? Losing weight after an actual failed prediction is relevant to
the question of which adviser gets these answers right; losing weight because
an adviser is unpopular is not thereby relevant. The proof shows exactly how
repeated contradictions affect performance and how false labels can spoil it.
This explains a substantive difference between correction and rationalization:
the update responds to publicly inspectable disagreements through an error
control argument, and the argument exposes conditions under which that response
misleads. It survives reversing which answer the learner wants to hear.

The method's mathematics can itself be checked from its finite rule and the
potential proof. That gives a reason to believe the performance theorem without
knowing an actual truth stream. For a concrete application, a useful basis for
feedback is an independent recount of a finite displayed list or a separately
checked calculation, rather than the expert's repetition of its own answer.
Such a check can settle the correctness of the representation **of the inspected
list or calculation** while leaving the reliability of a display, its relation
to an external object, and uninspected cases open. No claim that a particular
instrument has been empirically calibrated is made here. Agreement of copies
of one report is not an independent check. Actual low error can also be supported
by repeated appropriately independent cross-checks, but extending those checks
to a new task or horizon requires an explicit generalization argument.

This is a positive case for defeasible correction, not a proof that a short
track record warrants a numerical future corruption bound. Independent evidence
for e_i and k might be partial: a reason can favor investigation or tentative
use without justifying the categorical claim that the antecedents hold. The
method is not licensed merely because its parameters can be named. The ten-error
corollary is a genuine guarantee **if** its quantitative conditions hold; this
note supplies no empirical ten-error entitlement for an actual human inquiry.
The strongest remaining gap is evidence adequate for such conditions in a
selected real application. No numerical threshold is defined to be warrant.

The #930 note gives the prior positive argument for why a warranted indication
of error counts against an endorsed factual representation independently of
comfort. Its squared-error certificate and statewise coherence projection are
imported unchanged in this integrated result. They do not calibrate this
protocol's feedback. In particular an internally coherent binary prediction
can be false; the projection result does not already solve this task. We reuse
F6, STMT-THERE-ARE-EPISTEMIC-REASONS, as the accepted existential floor. Neither
that floor nor the performance algebra alone identifies particular reasons.
The [preconditions note](epistemic-reasons-preconditions.md) separately records
STMT-THERE-ARE-ORDINARY-ROLE-EPISTEMIC-REASONS and
STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS as OPEN. This
slice does not transfer F6 approval to either stronger claim; its restricted
reason-giving argument remains a defeasible philosophical defense.

## The decisive epistemic cases under this interpretation

| Case | Accuracy facts | What is and is not supported |
| --- | --- | --- |
| Relevant correction | False actual answer initially, reliable contrary labels, subsequent correct answer | The recovery theorem proves improvement in this case; independently warranted labels can give a reason to revise without exact all-state access. |
| Misleading evidence | True actual answer initially, same contrary labels, subsequent false answer | The no-go control permits error despite coherent agreement. Unrestricted reports do not warrant their own reliability. |
| Lucky accuracy | The initial true tie answer in an actually true world, before distinguishing evidence | The answer is correct. Its correctness alone supplies no evidence for the update rule or the expert pool. No random chance interpretation is encoded. |
| Reliable but not accessibly justified | A stream actually meeting the low-error conditions, while the agent lacks grounds for those conditions | The error bound holds extensionally. Internal entitlement does not follow from a secret fact about reliability. An externalist may regard reliable process history as sufficient for a different kind of warrant. |
| Justified but fallible | Independent checks give defeasible grounds to trust a label, yet this particular label is a rare false one | Such grounds can rationally favor revision under the proposed bridge while leaving the revised answer false. The trace proves compatibility of the accuracy facts, not that an arbitrarily stipulated agent is justified. Justification requires the independent grounds described in the case. |

These are distinctions with explicit countercases, not five new formal
`Reason` predicates. The last two rows disagree about the epistemic significance
of access; neither is settled by counting errors.

## Strong rivals and the remaining fork

Naturalistic reliabilism can take actual low error as central and use the theorem
without requiring agents to know a k. It still needs an applicable process and
reference class; realized accuracy of one trace does not establish reliability
across cases. An internalist can demand accessible grounds for treating the
feedback and expert pool as adequate. The proof supplies the connection but
not those empirical grounds. Skeptical or quietist inquiry can accept the
performance theorem while withholding the application premise, suspending
belief or continuing local testing. The indefinitely misleading trace is its
strongest control. A pragmatic view may prefer a comforting or coordination-
promoting policy even when it predicts less accurately; that practical advantage
does not change the error count. An epistemic objectivist can accept the
restricted warrant bridge without claiming every correction is true or that
truth has a theistic ground.

The strongest revisionary rival accepts all of the mathematics yet denies that
truth-relevant support is a reason unless truth is chosen as an end. The positive
case is that this leaves it unable to criticize a rationalization **as an answer
to the factual question** when the agent prefers it, despite a demonstrated and
independently supported tendency to make avoidable mistakes. That explanatory
cost is a reason to accept the restricted bridge. It is not a contradiction in
the rival, an automatic duty derived from the definition of belief, or a proof
of categorical authority. One can decline inquiry, suspend belief or have
competing practical reasons. Neither the mathematical guarantee nor actual
error alone refutes a coherent anti-normativist.

## Truth, appearances and ontology

An actual mistake requires the represented answer and its correctness to come
apart. It therefore rejects identifying correctness of **that answer** with
its being assented to. It does not prove that all truth is independent of all
mental activity: some questions concern thoughts. Nor does it entail material
external objects, a durable subject, God or moral realism. The truth stream
is an independently supplied evaluation, not a metaphysical reduction of truth
to a Boolean, a report, or a score. An appearance can be feedback; its occurrence
does not establish the existence of its apparent object. Having a current
representation does not establish an enduring concrete bearer. The existing
Cogito controls supply the relevant boundary: `CogitoSubject.subjectlessControl`
witnesses occurrence without a bearer when the bearer bridge is omitted;
`CogitoSubject.nonSubstantialBearerModel` witnesses occurrence and a bearer
without substantial subjecthood. `CogitoConcrete.omissionControls` separately
omits concreteness and existence-at-a-world bridges. These exact existing
proofs are in [CogitoSubject/Solution.lean](../../TruthCore/Results/Logic/CogitoSubject/Solution.lean)
and [CogitoConcrete/Solution.lean](../../TruthCore/Results/Logic/CogitoConcrete/Solution.lean),
under `TruthCore.Results.Logic`. They are reused as established limitations,
not re-proved or taken to show metaphysically possible subjectless thought.
No persistence premise appears here, so no durable bearer is inferred either.
The inquiry-access boundary is also retained; no new ontology follows from
this protocol.

## Reuse, proof boundary and premise comparison

The load-bearing seed was STMT-CORRECTION-CRITERION-EXACT-FACTORIZATION;
`related` and its dossier, the inquiry-access and both accuracy dossiers,
existing #934 comparison, previous attempts, and existing algorithm vocabulary
were inspected. No weighted-majority correction proof was found. New vocabulary
is specific to finite rational online updates; it does not replace truth,
warrant, normative reasons or the existing exact criterion.

The certificate binds one argument and composes the actual correction-criterion,
inquiry-access, expected-accuracy and statewise-dominance theorems. The new
protocol proof derives its conclusion from sums, inequalities and induction.
It is not a transcription. Formal assumptions are explicit quantified framework
inputs: finite expert advice, available feedback, a fixed binary truth
interpretation and horizon; the truth-relative bound additionally supposes a
corruption bound, and the numerical example a two-expert pool containing an
expert with at most two errors. No probability, perfect expert, future
stationarity, external-world ontology or normative premise is smuggled in.

Retained philosophical floor: F6's existence of epistemic reasons. Defended but
open application premises: independent grounds for relevant feedback/pool
adequacy, generalization to the selected inquiry, and the restricted reason-
giving bridge against the goal-relative rival. Added or removed root premises:
none; root closure: none. A conditional performance guarantee is real method
knowledge, not certification that these open premises hold. Exact frontier
costs and delivered-head check evidence are linked in the PR/current #931
handoff, which remains the single progress tracker. #931 stays open for the
remaining real-application warrant question. Next concrete step: select a
bounded factual application with independently inspectable feedback and compare
the evidence for its error/corruption regime against the skeptical alternative.

## Adaptive correction without an environmental restriction (#1058)

Truthful feedback alone does not guarantee eventual predictive success. The
new analyst construction takes any total deterministic method whose input is
the finite sequence of earlier true binary labels. Starting with the empty
history, let the next true label be the opposite of the method's prediction,
then feed that true label back. This recursively defines **one infinite
stream**, including all of its compatible finite prefixes. The proof identifies
the generated history at every round with the actual past of this same stream.
At every round the prediction is wrong; the existing `FallibleCorrection.mistakes`
counts exactly `n` errors in the first `n` rounds.

The quantifiers matter: for every method there is a method-dependent failing
stream. There is no claim that one stream defeats all methods. A method which
already encodes a particular stream can predict it; the diagonal for that
method would be a different stream. The construction assumes neither a bound
on computation nor a randomized method or chance distribution. It supplies
no probability that an actual stream is adversarial, and no conclusion about
expected stochastic performance.

The comparison with the positive result uses the **same** rational update and
voting functions. For a finite pool of history-based experts, `historyWeights`
reconstructs the original state by applying each earlier expert prediction to
its subsequent true feedback. `learnerAdapter` proves equality with the original
`learner` on the induced advice and feedback streams, for every pool size,
stream and round. No fresh weighted-majority rule or performance premise is
introduced.

For a pool of two experts, diagonalize that history-based weighted learner.
The original learner then makes eleven mistakes at horizon eleven, with no
false feedback. Importing the existing certificate's two-expert budget shows
that **each** expert must have more than two mistakes on that same prefix:
otherwise the learner would have at most ten mistakes. This is the concrete
two-expert/budget-two consequence only. A lower bound for arbitrary finite
pool sizes and expert-error budgets would need its own arithmetic argument;
it is not inferred from this instance.

The positive guarantee survives. Its good-expert coverage hypothesis cannot
hold on this adversarial prefix; that is a reason to inspect a proposed
environmental or rule-class restriction, rather than discard the theorem.
The unrestricted methodological skeptic and the restricted learner therefore
disagree about which streams and expert coverage are warranted for the inquiry.
Independent evidence about that applicability remains the philosophical bridge.
The diagonal does not prove that all methods are irrational, that actual
knowledge is impossible, or that epistemic reasons do not exist.

This also marks a boundary for a possible rule-following argument. Identifying
determinate semantic content with unrestricted next-case prediction would be
an additional premise. Failure to predict does not establish meaninglessness
or semantic indeterminacy. This mathematical result does not complete the
missing meaning-as-use/language-games coverage of #1010 or attribute a theory
to Wittgenstein or Hume. The existing Hume finite-prefix result remains a
distinct, weaker boundary; it was reused for discovery, not restated as the
all-horizon adaptive theorem.

The three result records are `ADAPTIVE-PREDICTION-DIAGONAL`,
`ADAPTIVE-PREDICTION-LEARNER-ADAPTER` and `ADAPTIVE-PREDICTION-TWO-EXPERT`.
Their definitions quantify the protocol inputs explicitly. Added/removed root
premises: none. Actual feedback warrant and normative authority remain open.

### Finite validation under explicit sampling (#1066)

The next positive step changes the empirical interface rather than assuming a
numerical expert-error budget. `FINITE-VALIDATION-SAMPLING` studies a finite
input domain with an arbitrary genuine Mathlib probability measure μ, a supplied
truthful Boolean labeling, and a finite hypothesis pool fixed independently of
validation data. Validation draws are the actual product measure μ^n, with the
same μ defining deployment error. Independence, truthful labeling and this
sampling/deployment alignment remain **OPEN** application bridges. Examples
include repeated independently drawn labeled cases from the intended deployment
population; convenient examples, selectively reported successes, feedback from
the predictor itself and a changing deployment population need not satisfy them.
No author attribution is claimed.

For a fixed hypothesis with actual error e, passing all n tests has probability
(1−e)^n. Applying Mathlib's finite union bound gives

`P(∃ h ∈ pool, error(h) > ε ∧ h passes) ≤ |pool| * (1−ε)^n`,

for nonnegative ENNReal ε≤1. The exact statement includes n=0, where the bound
can be uninformative, and the empty pool, whose false-acceptance event is empty.
When the numerical bound is below a desired risk tolerance, a procedure that
selects a passing member of this fixed pool, or abstains when none passes, has
that simultaneous false-acceptance control inside the sampling model. For
four predeclared candidates, ε=1/2 and ten tests give a bound 1/256. It need
not identify a good member beforehand. No perfect expert, realizability, or even
existence of a passing candidate is assumed. This is a substantive addition to
the earlier weighted-majority guarantee: observed validation agreement now has
a derived sampling relationship to actual distributional error, instead of
receiving an assumed expert-error budget. It does not establish that budget
with certainty or certify that the sampling model describes the actual world.

Selection within the pool is allowed; selection outside it changes the claim.
`FINITE-VALIDATION-SELECTION-CONTROLS` supplies four uniformly distributed points
whose truthful labels are all Boolean false. A memorizer predicts false at its
selected point and true at the other three. Its actual error is 3/4. If the selected point is the
one observed validation example, the memorizer always passes. The probability
of this posthoc bad-pass event is 1, exceeding the incorrect singleton bound 1/2
at ε=1/2. The singleton was chosen from the same validation data, so the
fixed-hypothesis theorem cannot be applied as though it had been fixed first.
Including all four memorizers in the predeclared pool restores the applicable
cardinality penalty, which here gives an uninformative bound 2. This control does
not deny valid selection among members of a predeclared finite class.

The frequentist joint bound also does **not** automatically say
`P(error≤ε | passed) ≥ 1−δ`. In the same uniform model, fix one memorizer before
sampling. Its error is deterministically 3/4, but its pass probability is
(1/4)^n, strictly positive for every finite n. Its bad-pass event at ε=1/2 is
exactly its pass event. Thus a rare pass can still be a pass by a bad candidate;
conditioning on that pass does not by itself make this fixed bad candidate good.
The checked artifact proves the event equality and positive probability, without
introducing a prior on hypotheses or pretending to calculate a posterior. A
small joint false-acceptance probability is useful procedural risk control; a
posterior or accessible-warrant interpretation requires additional premises.

The strongest rival remains that representative independent validation itself
has not been warranted: adversarial sequences, distribution shift, systematic
label corruption or unrestricted posthoc selection can break the application.
The existing adaptive diagonal concerns unrestricted deterministic prediction
against predictor-dependent streams, rather than this fixed iid sampling
profile. The existing Hume finite-prefix alternatives remain compatible with
finite probabilistic risk control: no finite sample guarantees every future
case. The accuracy theorems likewise evaluate supplied probabilities and do not
supply this sampling-to-reality bridge. Neither those results nor the new bound
vindicate induction generally, establish categorical epistemic authority, or
change F6 or any root-frontier premise. The positive philosophical payoff is a
calibrated testing procedure *within stated assumptions*, with an explicit
remaining burden to justify those assumptions in a concrete inquiry.

The frozen Challenge and Solution use the same two advertised proposition
heads, `SamplingCertificate` and `SelectionControls`; the sampling assumptions
are universally scoped inside the former rather than hidden corpus premises.
Only the new finite-validation vocabulary, results and records, this existing
note, and generated import lists are changed. Source attribution is deferred.
