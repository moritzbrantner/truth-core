# Carneades induction intake: predicate basis (2026-10-28)

Scope: a bounded science/induction investigation, separate from higher-order
justification and from the Catholicism root routes. No root premise change.

## Consulted witness and attribution limits

Read the entire public English `en-orig` automatic-caption stream of
**Swinburne's Objection (To The New Riddle of Induction)**, Carneades.org,
https://www.youtube.com/watch?v=ye9qprxFP28 , 00:00–03:40.
The downloaded metadata names the Carneades.org channel. Reproduce with:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-induction.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=ye9qprxFP28'
```

Consulted VTT SHA256:
`b90376d020ab32f232785fa2b373a8d90b7b2d0defb699d368ebd90d8c994cd4`.
This identifies the consulted download, not a `span_sha256` or successful
materialization. No audio/slides verification, authenticated media export,
passage manifest or attributed corpus claim was completed. These are provisional
readings of the channel narrator, not findings that the historical authors held
precisely the narrated views. Captions visibly garble names and grue/bleen.
Do not promote these notes to source claims without a materialized media witness
and checking the decisive wording against audio. Complete transcripts are not
committed.

## Full-stream reading

- **00:00–00:43:** introduces this as the third induction video and an
  introductory presentation of an objection to the new riddle; recommends
  further reading. The exposition is not offered as a primary text.
- **00:43–01:12:** recalls the green/grue choice and entrenchment as an answer,
  then introduces a proposed stronger reason. The caption around 00:55 appears
  to reverse the preference direction; the following explanation explicitly
  associates entrenchment with the familiar green predicate. Do not base any
  claim on that isolated caption sentence.
- **01:13–02:10:** presents the objection that grue has a disjunctive definition
  while green does not, then the reply that green can be disjunctively expressed
  using grue/bleen. The relevant issue is dependence on a chosen primitive
  vocabulary, not whether disjunction is logically defective.
- **02:10–02:47:** introduces a qualitative/locational distinction, explaining
  the former as independent of time/place and the latter as dependent on them.
- **02:47–03:28:** motivates preferring qualitative predicates by contrasting
  whether a clock/location is required to classify a color; concludes with a
  preference recommendation between otherwise equally possible predicates.
- **03:28–03:40:** announces a forthcoming reply and closes. That reply was not
  read and is not inferred from the announcement.

## Reuse, strongest rival and bounded control

Dossier inspected: `STMT-HUME-INDUCTION-TESTS`. Existing
`TruthCore.Modern.Hume.Induction.Checks` and
`TruthCore.Results.Modern.Hume.Induction.checks` already cover finite records,
next-case underdetermination, intervention records and explicit normative
bridges. Repeating another delayed-failure sequence would add nothing.

The strongest rival here says the physically relevant feature basis is
independently available through measurement, perceptual capacities or a theory
of natural properties. Then invariance in that basis can matter even though
arbitrary recodings exist. A pragmatic rival can prefer a vocabulary because it
is easier to measure or use. Neither rival requires deductive certainty about
all future cases. The video's preference recommendation does not itself supply
a machine-checkable defense of these physical or normative standards.

`STMT-SCIENCE-PREDICATE-RECODING` instead fixes an explicit small semantic
profile: Boolean phase and Boolean feature, complementing the coordinate only
in phase true. It proves that recoding is involutive and that transporting a
predicate preserves its values at corresponding recoded coordinates. It also
proves that phase independence is exactly factorization through the original
feature, while the base feature predicate's transported expression fails the
fixed-coded-coordinate independence test.

The original and recoded tests hold different coordinates fixed. Thus the
failure is a control against an unqualified coordinate-based definition, not a
contradiction between equivalent descriptions. The proof chooses no privileged
physical basis, and does not settle projectibility, actual color behavior,
probability, inductive entitlement or the rationality of science.

Rejected readings: inability to deduce continuation does not imply irrational
induction; reversible coding does not show all predicates equally useful;
syntactic disjunction does not establish physical dependence; Boolean phase is
not examination history, continuous time or Goodman's full grue definition.
The recoding control is a stipulated mathematical investigation motivated by the
reading, not attributed source formalization. Its vocabulary is new because the
existing Hume traces represent episode outcomes, not feature-coordinate changes.

## Verification and remaining obligation

Shared development endpoint: `http://127.0.0.1:8765/lean/diagnostics`, workspace
`/home/brantner/privat/truth-core-sprint-proof`, session `causal-harvest`, unique
path `Scratch/carneades-induction.lean`, exclusive `/tmp/truth-core-lean.lock`.
Combined exact vocabulary/proof content (only the local import removed) returned
no diagnostics at service HEAD `49b4589aa6744c91a6bc9adec13215d0e7245c9d`,
content SHA256 `16a36f041b1e48444ba1c91e6b9c6754d9e7260c7428da5cbddece1f6839fd5a`.
This is development evidence only; final CI must supply module build, binding,
Comparator, zero-axiom and NanoDa checks before mechanical verification is
advertised.

Premise comparison: the control has no philosophical premises and adds no root
route. It discharges only its bounded mathematical statement. Selecting a
relevant feature basis and defending its epistemic/pragmatic preference remain
open obligations, with no new source support claimed. Next useful step is an
independent source defense or criticism of that selection criterion, rather than
another finite-prefix countermodel or an assumption that simply selects green.

## Logic-first extension #1036 (2026-11-05)

Owner direction supersedes the previous next-step recommendation: investigate
this working argument logically; historical attribution is deferred. No new
source, passage or claim is needed or asserted. The provisional caption findings
above remain provisional, including their rejected readings and witness limits.

The checked argument is now `SCIENCE-INDUCTION-SELECTION`, vocabulary
`TruthCore.Science.InductionSelection` and theorem
`TruthCore.Results.Science.InductionSelection.certificate`. It imports and uses
exactly `TruthCore.Results.Science.PredicateRecoding.controls` and
`TruthCore.Results.Modern.Hume.Induction.checks`; the original controls are not
reproved. New vocabulary is needed because the earlier two-coordinate predicate
test has no evidence space, hypothesis response or selection operation.

Let rE and rH be supplied invertible recodings of evidence and hypotheses.
Neutrality says `answer (rE e) (rH h) ↔ answer e h`. If `rE e = e`, substitution
makes the response closed under rH. If the response contains exactly h, closure
forces `rH h = h`. Consequently a moved hypothesis cannot be uniquely selected.
For deterministic total selectors, fixed evidence and equivariance force the
chosen output to be fixed; adding that the output moves gives a contradiction.
This is a general constraint, not an assumption that the desired conclusion
already follows. Invertibility is encoded by Mathlib `Equiv.Perm`; the proof
actually needs only the specified covariance and fixed-input equations.

The explicit omissions use the same two-hypothesis swap:

- **Evidence not fixed:** two evidence states exchanged with the hypotheses;
  the identity selector is unique and equivariant. This additional evidence
  discriminates the rivals, unlike their common finite prefix.
- **Choice not equivariant:** one evidence state and a constant unique choice.
  That choice is coherent but fails the recoding test. It establishes neither
  actual green's privilege nor a justification for arbitrary preference.
- **Response not singleton:** selecting both hypotheses and selecting neither
  are neutral. The theorem proves these exhaust neutral responses for this
  two-hypothesis profile. Neither is a contradictory or empty-carrier model.
  Empty response is abstention, distinct from an empty evidence/hypothesis type.

The observation instantiation is not merely a new finite-prefix counterexample.
For every n, evidence is an actual function `Fin n → Bool`. Candidate h predicts
true at each index below n and h at every later index. Existing feature recoding
is applied with phase `n ≤ i`. Restriction to the first n outcomes commutes with
that recoding, while the full recoding exchanges the candidates and they disagree
at n. Compatibility is exact observed-record equality and is neutral. The general
obstruction therefore excludes **every** neutral singleton response at that
record and **every** equivariant total selector on that evidence space. Both
candidates fit, supplying nonvacuity; the false-tail candidate is definitionally
the existing Hume `delayedFailure n`, not newly invented trace vocabulary.
The n=0 case remains a valid empty-record instance on inhabited carriers.

An added criterion can break the symmetry without being smuggled into the data.
`Uniform trace` says all outcome coordinates agree. For n>0, uniformity of the
original-coordinate candidate holds exactly for h=true; applying uniformity to
the recoded candidate holds exactly for h=false. The original criterion fails
neutrality under the candidate swap. This is a substantive comparison of two
criteria on complete predictions, rather than defining green as preferred.
The positive-prefix hypothesis matters: with n=0 both candidates are constant.
A measurement, natural-property or pragmatic basis can endorse one criterion as
an additional commitment. The theorem neither defends nor refutes that
endorsement and does not identify representation changes with physical changes.

Claim/type self-sweep: results concern a supplied mathematical representation
and conditional selection discipline, not actual color laws, probabilities,
inductive entitlement or historical doctrines. Reject the inferences from
finite-data uncertainty to irrationality, reversible coding to equal usefulness,
and syntactic disjunction to physical unnaturalness. No combination of these
logical constraints independently establishes a physical/projectibility basis.
A basis-sensitive practical decision can coexist with the logical obstruction.

Development: the shared preview returned the correct HEAD/session/content
binding but could not import the old cached non-module PredicateRecoding from
our module. No preview changes were made; canonical CLI fallback built both new
modules successfully. The frozen Challenge and Solution have the same advertised
`Certificate` type. Final CI retains the build, binding, axiom, Comparator,
NanoDa and integration gates. Reproduce affected verification with:

```sh
python3 scripts/worker_env.py -- lake build TruthCore.Results.Science.InductionSelection.Solution
python3 scripts/worker_env.py -- python3 scripts/corpus.py bind-check --result SCIENCE-INDUCTION-SELECTION
python3 scripts/worker_env.py -- scripts/verify-result.sh SCIENCE-INDUCTION-SELECTION
```

Premise comparison: no ordinary corpus premises added or removed. The new
certificate derives conditional constraints and witnesses alternative
configurations; its fixed evidence, neutrality and moved-output conditions are
locally quantified, not independently established commitments about science.
All Catholicism root-route premises, route costs and closure obligations remain
unchanged; this bounded science result closes no root leaf. Remaining gaps are
actual applicability of a supplied symmetry, an endorsed physical/measurement
basis and any epistemic or practical bridge. Attribution remains deferred.
Shared convention resolution sourceRevision:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

## Degree-bounded laws #1395: proposed outcome for independent challenge (2026-11-11)

Analyst reconstruction, attribution deferred. Baseline actual main
`0e000912934179064919bca5e3e29a3fcb913ddd`. The new
`PolynomialInduction.Certificate` is separate from the frozen #1036 result.
It serves the proposed evidence-justification connection to #931 truth access,
not an existing polynomial-to-Catholicism route. The exact existing
`TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.boundary` requires
truth to be constant on equal-report states for an exact truth classifier.
Polynomial evaluation can distinguish *coefficient models inside a stipulated
class*; applying this to historical/metaphysical truth needs a model-to-content
truth map, warranted class membership and faithful measurements. These bridges
are unbuilt. No actual root-facing evidential premise is discharged.

### Meanings, proof scope and discriminating controls

`Identifiable s d` universally compares two coefficient polynomials over a
commutative integral domain with `natDegree ≤ d`, agreeing at every point of
`Finset s`. Finset membership supplies distinctness: repeated measurements do
not increase this cardinality. Zero is included (`natDegree 0 = 0`). This is
injectivity, not surjectivity onto arbitrary observations, existence of a true
law, numerical conditioning, approximate fit, causal identification or warrant.
`vanishing s` is the monic product of `X-C x`; the empty product is one.
These are completed stipulative mathematical definitions; physical law,
measurement fidelity and admissibility remain explicit application obligations.
No opaque physical predicate is asserted by the certificate.

The threshold is `d < s.card`, equivalently at least d+1 distinct inputs.
Forward uniqueness reuses Mathlib
`eq_of_natDegree_lt_card_of_eval_eq'`; the converse compares the monic product
with zero when `s.card ≤ d`. This handles empty observations and d=0 without a
special nonempty-data premise. No infinite-field assumption is needed, and even
field division is unnecessary: integral-domain root counting suffices. This
states sufficient weaker algebraic assumptions, not a classification of every
ring where some individual instance happens to be injective.

The fresh-point theorem compares arbitrary p with p+vanishing s. It proves
observed equality and unequal values at any supplied `a ∉ s`; no infinitude is
needed *given* that point. An infinite domain guarantees availability beyond any
finite s. On a finite field with all elements observed there is no fresh point.
Moreover coefficient identity differs from function equality: over F_q,
X^q-X is nonzero as a polynomial but evaluates to zero everywhere. Thus failure
of coefficient identifiability does not imply that a new field input remains to
be predicted. The earlier 24 F5 checks are no global proof and are not used.

The rational control computes p=x² and q=x²+x(x-1)(x-2)(x-3): agreement at
0,1,2,3 and predictions 16/40 at 4. Both are polynomials (hence smooth/analytic
on the reals), so merely imposing smoothness/analyticity does not select p.
At degree bound two, the four points identify p; removing that class restriction
admits q. Existence remains separate: degree-zero polynomials cannot fit outputs
0 at input 0 and 1 at input 1, despite two samples exceeding the threshold.
That elementary observation is explanatory prose, not an extra certified result.

Affine substitution `p.comp (C a * X + C b)` preserves natDegree when a≠0.
This is the exact class map: for z=a*x+b the transported law is
p((z-b)/a), and the inverse substitution is a*z+b, so the two degree-bounded
classes correspond. The certificate proves degree preservation, not a new
physical symmetry or an independently warranted coordinate group. Zero slope
collapses a nonconstant polynomial and is deliberately excluded.

The real map z=x+x³ is proved injective using the positive factor
1+x²+xy+y² and surjective using continuity and the intermediate value theorem.
The displayed law has degree three in x and degree one as y=z in z. This does
not say that composition with its inverse preserves polynomial form for every
law: transporting an entire class and reapplying the same numeric degree cutoff
are different operations. Arbitrary invertible recoding does not preserve the
stipulated low-degree class. The certificate uses actual real bijectivity, not
an unexplained coordinate permutation or a finite test.

#1036 proves closure/fixed-point constraints conditional on supplied fixed data,
neutrality and moved candidates. Its Boolean cutoff model and uniformity test
are not general polynomial degree theorems, physical symmetries or norms.
We reuse its already checked scope rather than claim polynomial p→p+r is an
involution or preserves H_d. Its positive asymmetric-evidence, basis-sensitive
choice, set-valued and abstaining controls remain intact.

### Positive rivals and further preconditions

**Structural physical modeling:** conservation laws, dimensional structure,
mechanisms and independently calibrated measurements can restrict the class and
admissible coordinates. Polynomial uniqueness then supplies a real conditional
inference. The remaining tests concern whether those constraints independently
exclude the added product, remain stable in the prediction regime, and survive
measurement error. Arbitrary recodings alone do not defeat such a defense.

**Bayesian comparison:** a likelihood/noise model and prior can rank compatible
models without deductive uniqueness. Descending into its preconditions exposes
prior mass, likelihood calibration and misspecification, rather than an assumed
requirement of certainty. Transporting both prior and likelihood under a
bijection preserves the comparison; imposing a fresh simplicity prior in the
new coordinate changes assumptions. No particular weighting is installed here.

**Predictive/pragmatic methods:** held-out error and online regret can justify
performance relative to a loss, comparator class and regime assumptions, without
identifying a true law. Their discriminating next test is robustness when the
regime or comparator changes, not another agreement-on-training-data example.
A regret guarantee is not a bridge to metaphysical truth or actual causation.

**Underdetermination:** unrestricted exact polynomial fitting preserves a
fresh-point rival, but does not show every rival has equal probability, predictive
performance, measurement accessibility or warrant. Its positive option is to
withhold a unique deductive law while permitting conditional or fallible
prediction. Neither irrational-science nor true-law-from-uniqueness follows.

### Complete proposed provisional judgment and reopening conditions

The mathematical identification claim has a general Lean derivation under the
explicit integral-domain/class/data assumptions, with empty-data and recoding
controls; final repository certification is reported in the PR. The result
supports conditional model identification. Current evidence does not select an
actual physical degree cutoff, coordinate privilege or epistemic norm, and does
not discriminate the positive methods above as a universal winner. This is an
assessment of present support, not proof of their impossibility or equal merit.

Strongest standing response is independently constrained physical modeling,
possibly combined with calibrated Bayesian/noisy prediction. Its price is
empirical/structural support for the constraints, calibration and extrapolation
regime; none is called unreasonable. A materially different next investigation
would fix an actual evidential target from #931, its measurement protocol,
admissible transformations and truth-content map, then test the excluded rival
against that evidence. This requires selection of a concrete application beyond
the supplied abstract polynomial task; inventing that applicability is withheld.
Evidence that measurement structure independently selects a class/group would
strengthen applicability; a robust rival satisfying those same constraints
would weaken identification. Discovery of an encoding mismatch would suspend
the mathematical interpretation pending repair. Independent semantic challenge
by the master must examine this complete proposed judgment before integrating
its consequential conclusions. No new owner assent, source claim or root route.

Claim/type self-sweep: every universal is inside the explicit coefficient-model
class; the fresh-point hypothesis is retained; exact values are rational;
bijectivity is real; affine slope is nonzero. No existential fit inferred from
injectivity, coefficient equality conflated with finite-field function equality,
or physical/practical warrant inferred from algebra. No old frozen proof edits.
Convention sourceRevision: `625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
