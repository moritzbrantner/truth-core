# Contrastive worldview justification: evidence, inheritance and authority

Issue #934. Analyst formulations, attribution deferred. No historical attribution,
new source reading, witness or authorial intention is asserted here.

## Argument and strongest alternative

The target is a *contrastive* public claim: reasons favor W over incompatible V.
The strongest charitable demand is to expose the comparison inputs and rule so
that someone outside the community can assess the inference. It is not a demand
that every outsider agree, that W have one unique selling point, or that every
true worldview be publicly distinguishable. A sufficient bundle of evidence can
be distributed across several observations; the present likelihoods concern one
received event, which may itself encode that bundle. Independence of constituent
observations is not assumed, and their likelihoods must not simply be multiplied
without an independence argument.

The decisive bridge is a **declared Bayesian update policy**, not an axiom named
“public justification requires discrimination.” For two mutually exclusive,
exhaustive hypotheses, let p be the prior for W, and a and b the likelihoods of
the same received evidence under W and V. Inputs are rational, 0<p<1 and 0<a,b≤1.
The normalizer is Z=pa+(1-p)b. The policy computes P(W|E)=pa/Z and
P(V|E)=(1-p)b/Z. Mathlib supplies rational ordered-field mathematics rather than
a new probability library. This bounded two-hypothesis parametrization is not a
generic worldview scorer and does not independently establish Bayesianism.

`updateConstraints` derives Z>0, normalization, posterior odds = prior odds ×
likelihood ratio, and three comparisons:

- **Evidence support:** P(W|E)>p iff a>b.
- **Posterior winner:** P(W|E)>P(V|E) iff pa>(1-p)b.
- **Evidence-only balanced comparison:** if p=1/2, a posterior win iff a>b.

If a=b, P(W|E)=p. A strict posterior preference then requires p>1/2. Thus the
strongest opposing reading is correct: an asymmetric inherited prior can justify
an asymmetric posterior *relative to that prior*, even with nondiscriminating
new evidence. It cannot attribute that asymmetry to the new evidence alone.
With p=1/10 and likelihood ratio three, W rises to 1/4 but still loses. A
likelihood advantage is neither a posterior win nor actual truth.

These are conditional mathematical constraints. Taking the inputs as rationally
warranted, sufficiently comprehensive and publicly available requires additional
epistemic premises. Neither unexamined priors nor equal priors are declared
mandatory. Dogmatic priors, impossible observed evidence, more than two
alternatives and imprecise probabilities are outside this certificate.

## What can settle a disagreement between coherent systems?

Analyst investigation, attribution deferred. Read coherence as satisfiability
in a common interpreted language. Let background B be the commitments shared
by two theories. If B together with the first theory has a model satisfying P,
and B together with the second has a model satisfying ¬P, then B entails neither
P nor ¬P. Each witness satisfies B and falsifies one of the proposed entailments.
Coherence of several theories by itself is weaker: they could be compatible
extensions, agree on P, or express the same view in different vocabularies.
The obstruction concerns a specific disagreement under a specified background.

Adding an independently warranted premise can settle that disagreement
deductively. If B and the added premise jointly entail P, the rival that
entails ¬P is excluded relative to the enlarged background. The added premise
could be a report of an observation or a separately defended a priori
constraint. If the rivals exhaust the live options and one survives, this
selects a theory relative to those inputs. Without coverage, the exclusion
stands while the surviving theory may still have other rivals. An a priori
argument must expose its premises and their warrant just as an empirical
argument must expose its evidence and how it bears on the rival.

### Test on a cosmological premise

The open root-route premise
[STMT-LOCAL-CAUSAL-PRINCIPLE](../../corpus/statements/local-causal-principle.json)
says every existing contingent individual at every world has a distinct
existing cause. Compare the single-form brute and ground policies in
[ActualWorldGap](../../TruthCore/Explanation/ActualWorldGap.lean), with
universal accessibility. At each shared world index, restrict the record to the tagged member
population and edges with two tagged member endpoints. The definitions of `present` and
`causes` give exactly the same record in both policies. Every tagged member
exists only in worlds with its own tag and is therefore contingent in this
frame. In the ground policy, `none` exists at every world and causes each
tagged member. In the brute policy, the member with index zero has no cause:
`none` is absent and there is no single-form member edge into zero
(`no_edge_zero` in the [solution](../../TruthCore/Results/Explanation/ActualWorldGap/Solution.lean)).
This is a structural comparison using the existing fixture. The claim about
the causal premise is an inspection of its definitions in that fixture.
The registered `controls` theorem checks the cross-policy member-edge
agreement and separately checks explanation properties, which use a different
relation.

The tie depends on what the record includes. An independently warranted report of a distinct existing cause for the
index-zero member at even one world would exclude this specific brute fixture.
Access to the extra bearer or its causal edges would also distinguish the pair. A defense of universal
causal coverage from shared commitments could also exclude the brute fixture,
if the defense reaches its very first member. Repeated observations of
members that already have member causes leave that step open. The strongest
live rival here accepts the same local causal structure among members and
allows an uncaused contingent source. Its cost is a limit on causal coverage.
The ground policy owes a defense of its extra bearer and why that bearer
qualifies as a cause in the intended metaphysical sense. The test leaves the
actual warrant for the root-route premise open. Neither policy is an
exhaustive theory of reality.

### Provisional judgment

Coherence is a condition on a theory, while settling a disagreement calls
for reasons that distinguish the rivals on the disputed point. Those reasons
may support a deductive exclusion, a defeasible preference, or continued
suspension. Within the existing Bayesian profile, even two rivals that both
allow the observed event can assign it different likelihoods. The evidence
can then raise one rival’s credence above its own prior even if the other
retains a higher posterior. Equal likelihoods preserve prior odds, and equal
likelihoods for one event leave future discriminators open. A tie gives no
reason to force an adoption or assign equal credence.

A premise can be fundamental to a theory in the sense that the theory assumes
it and it does not follow from its other specified commitments under the
stated consequence relation. The same premise could
be a consequence of independently motivated commitments in a different
account. The stronger claim that it has no independent warrant needs a
separate argument. Likewise, whether the actual order has an ultimate ground
is a question about reality, whereas whether we can identify that ground is
a question about our reasons. The next test is to identify independently
warranted evidence bearing on a case where the rivals disagree. Warrant for the universal causal premise
would additionally require an argument covering unobserved cases and worlds.

## Birthplace swap and inherited information

`identityControls` checks two different transformations. Merely changing a
speaker/community label leaves the entire Comparison fixed; `publicAssessment`
is invariant by its declared input signature. Relabeling W and V instead
complements the prior and exchanges likelihoods, and genuinely swaps the two
computed posteriors. Relabeling only the likelihoods while secretly retaining
the original privileged prior is not the same transformation.

The unique-neutral-answer obstruction is imported from
`TruthCore.Results.Science.InductionSelection.symmetry` (#1037), instantiated on
its Unit-evidence, Bool-hypothesis swap. No second generic symmetry proof is
introduced. A set-valued neutral answer may admit both rivals or abstain; it
cannot uniquely admit a hypothesis moved by a swap that fixes all evidence.
An asymmetric prior, informative report, unequal access or expressly chosen
standard can break this symmetry, but must be listed as an input.

The controls distinguish four claims instead of identifying them:

| Case | Checked behavior | Boundary |
| --- | --- | --- |
| Equal evidence, inherited p=3/4 | Posterior stays 3/4 | Inheritance is an input, not evidence advantage or proof of falsity. |
| Reliable inherited testimony | Each true-state row sums to one; correct report rate 3/4; hearing W from balanced prior gives 3/4 | Cultural transmission can carry information. No actual tradition's reliability is asserted. |
| Misleading report from that same channel | W wins while V is actual; the received W report has positive likelihood 1/4 under V | Reliability is not factivity; posterior preference does not guarantee truth. |
| False attractive W | W is attractive and posterior-favored, while V is actual | Attraction, acceptance and truth remain distinct fields. No causal sociology is encoded. |
| Indistinguishable truth | Two actual-truth assignments share exactly the same Comparison | One alternative is true in each case; public comparison data need not distinguish it. This is not global skepticism. |

The data input is a supplied numerical comparison, not a claim that agents can
observe true likelihoods. The channel controls model one report and its
truth-conditioned distribution, not repeated independent testimony, transmission
chains, justified calibration, access to reliability or knowledge.

## Outsider assessment and self-authorization

`insiderStandard community proposal` is the coherent membership rule that a
community authorizes its own labeled proposal. Each community passes its own
rule; the two disagree about one fixed proposal. The resulting standard is not
identity-independent in the public sense defined above. That is a proven
**mismatch with the proposed public policy**, not a contradiction in the
membership rule. It may be entirely appropriate for choosing a club's uniform
or membership convention; that purpose supplies no comparative truth advantage.

A premise argument “our authority is true because our authority licenses that
very claim,” with no independently accepted input, is premise-circular as an
attempt to supply an outsider with a reason to accept its starting premise.
The finite membership control does not prove every use of inherited rules is
vicious. Using an inference rule while defending it may be rule-circular; a
foundationalist may explicitly accept a stopping point. Neither entails a
logical contradiction merely because an outsider declines the standard.
Public intelligibility here means identifiable premises and a comparison rule,
not persuasion, psychological access, justified acceptance or universal assent.

Issue #932 is still open at the inspected baseline and has no published comments;
this work does not treat its intended authority bridge as an established result.
It reconciles its distinction by importing the already checked results rather
than inventing a fresh opacity model:

- `CorrectionCriterion.characterization` separates exact data classification
  from warrant. Equal-data/different-truth states obstruct an exact classifier,
  not every fallible entitlement.
- `TranscendentalPractice.InquiryAccess.boundary` preserves the two directions
  of independence between exact access and truth-directed selection.
- `TranscendentalPractice.AgencyDuty.boundary` supplies an inhabited successful
  practice with the same behavior and opposite categorical duty assignments.
  The local membership convention adds no bridge excluding that authority gap.
- `ReflectiveCoherence.TruthDirected.truthDirectedReflectiveDuty` gives the
  positive conditional: a duty true at an actual world plus an independently
  truth-directed selection policy yields duty compatibility. Neither premise
  is inferred from public comparison or merely giving reasons.

**Performative contradiction** requires simultaneously accepting the same public
invariance rule and a contrary verdict on identical inputs. The theorem refutes
that precise bundle, not every attempted advocacy. An advocate who explicitly
chooses a local rule and withholds categorical authority remains coherent.
Calling a policy “evidence-only” while relying on a hidden prior can be
self-undermining as a description of the policy. Wanting public approval while
refusing the audience's comparison standard can be pragmatic tension. Divergent
open priors or standards can be ordinary disagreement. None of the latter three
is automatically a contradiction. PSR-self-application (#756) remains a distinct
reason-for-belief versus reason-why-fact boundary; no epistemic-to-ontic reason
bridge is introduced.

## Serious rival completions

These are analytic profiles, not historical attributions or exhausted theories.

| Profile | Reading of the same cases | Remaining burden |
| --- | --- | --- |
| Naturalistic reliabilism | The calibrated testimony channel can warrant inherited belief even without reflective access to its reliability. | Establish actual reliability and the selected warrant standard; channel truth is stipulated here. |
| Internalist evidentialism | An agent may lack justified access to the supplied likelihoods or reliable channel, despite its actual reliability. | Explain the accessible support and prior entitlement; no access field is smuggled into Comparison. |
| Social/practice constructivism | Public invariance can govern participants who adopt that practice; a club's membership rule has a narrower legitimate scope. | Derive categorical reach if claimed; coherence of local convention is retained. |
| Expressivism/quietism | A comparison rule can express an adopted policy while categorical metaphysics is withheld. | Account for policy criticism and disagreement; the arithmetic still holds conditionally. |
| Skeptical underdetermination | Identical comparison data leave actual truth unsettled in the two truth assignments. | This defeats exact discrimination here, not every practical or fallible justification. |
| Objective realist/theistic account | Publicly binding reasons may have categorical authority and a deeper ground. | Supply authority, grounding and theistic uniqueness bridges; neither normalization nor identity invariance does so. |

## Composition, premise comparison and self-sweep

`LOGIC-CONTRASTIVE-WORLDVIEW` explicitly composes the new core inference with
four existing inference applications for the imported boundary propositions.
The Solution actually imports and calls the exact existing Lean theorems.
`Certificate` binds the resulting conjunction; its new arithmetic and finite
controls are not a transcription of a supplied conclusion-containing premise.
The graph does not add a metaphysical or root edge merely for connectivity.

All advertised universal claims quantify over the specified rational inputs,
policy or supplied recoding; the finite fixtures witness exactly their listed
fields. The two exhaustive hypotheses are model hypotheses, not the full set of
real worldviews. No newly attributed source claim or self-evident marking exists.
The declaration of an ignored community argument is an explicit policy choice,
not an empirical theorem about human impartiality. The local convention's
failure of public invariance is not a refutation of local standards. Reliability
is conditional distributional accuracy, not guaranteed true report or knowledge.

Formal assumptions retained: non-dogmatic positive rational prior, positive
bounded likelihoods for one event, the two-hypothesis exhaustive profile and the
specified Bayesian update/comparison policy. Their interpretation, warrant and
real-world applicability remain open; categorical authority and any objective
or divine grounding require separate premises. No root premise is discharged,
no root route is introduced, and the prior root-reaching open leaves are
unchanged. Baseline and delivered frontier commands are recorded in PR evidence.
The convention stack used source revision
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

## Preview experiment

The coordinator-owned service accepted the full vocabulary submission at
`Scratch/worldview934/Vocabulary.lean`, bound to preview HEAD
`a2d97ecf1429e86b3e12f15b91b735f85e27822e`, session `workloop-20261105`,
dirty hash `b93379e082a28681a60b563d432638de2e16611a00a5d34fc322e5c9df65a3ec`
and submitted-content hash
`d08ddfe2efbe9df8187a9707d96d1b2aa7573d44f50999bae311d8be7075146b`.
It returned missing dependency/module diagnostics: the public-main dependencies
were absent in the older preview, and the first candidate also used an invalid
Rat import, corrected in the canonical clone. This is not successful proof
feedback. The request took approximately 0.98 seconds with negligible lease
wait. Continued through the CLI with built imports, without restarting or
refreshing the shared service. Recommendation: **revise** preview dependency
alignment before retaining it for this lane; CLI remained sufficient and the
preview did not block the logic. Comparator/NanoDa and delivered-head CI remain
the final verification authorities.
