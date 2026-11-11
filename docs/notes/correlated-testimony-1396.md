# Correlated testimony: exact corroboration and process warrant (#1396)

This is an analyst reconstruction of general report confirmation, connected to
#934/#931 only by a **proposed, unbuilt epistemic-warrant bridge**. It is not an
existing root route. The exact proposed parent is #934 standard
`0bddef38-034f-58f3-9920-078fa893252c`: a warranted correlated-report
update bridge would have to justify actual dependence/process calibration and
the policy-to-warrant inference. It is **UNCONNECTED to the root** until those
bridges are justified. Merely composing probability mathematics earns no root
route or discharge credit. The owner excludes Bayesian/probabilistic scoring from
historical stages 4–6: none of these tables scores Resurrection, any historical
religious rival, or actual witnesses. No root premise is discharged.

## Meaning and reuse

`TruthCore.Logic.CorrelatedTestimony1396.Reports` gives a non-dogmatic rational
prior and two four-cell rows, one under H and one under notH. Each row is a
partition of report receipt (AB, A-only, B-only, neither), strictly positive and
normalized **within** its hypothesis. H/notH are the stipulated exhaustive
binary comparison, not an exhaustive account census. `comparison` uses the
existing `ContrastiveWorldview.Comparison` type and its exact update theorem
(`Results.Logic.ContrastiveWorldview.updateConstraints`; core statement
`0bddef38-034f-58f3-9920-078fa893252c`). This is
EVIDENCE_SUPPORT_VERSUS_WORLDVIEW_TRUTH_1. Posterior support means increase in
this model's assigned probability, not posterior victory, truth, accessible
reliability or categorical obligation.

`conditionalH/V` mean A given B within the corresponding hypothesis;
`pooledConditional` means A given B in the **same prior mixture**. Swapping A/B
changes both rows, preserving the prior. Independence means an explicit product
identity. A row/table is no causal explanation; reading those equations as actual
report-process facts remains OPEN. Zero-cell and degenerate-prior cases are
outside this theorem, rather than silently divided by zero.

## Exact consequences

The frozen Challenge/Solution certify:

- `criterion`: joint improves on B iff P(A|B,H)>P(A|B,notH), equivalently
  P(A|B,H)>P(A|B). Joint improves on **both** iff this and the swapped criterion
  hold. BF(AB)=BF(B) times the conditional A-given-B likelihood ratio; instantiating
  at `Reports.swap` gives the other chain ordering.
- `independenceSuffices`: conditional independence within H **and** within notH,
  together with each report's individual support, implies improvement over both.
  Both independence equations are hypotheses; no independence default is proved.
- `controls`: four exact nondegenerate models below. All 32 row cells are positive,
  and every row sums to one by the `Row` constructors. These are direct Lean
  arithmetic proofs, not certification of finite enumeration output.

Each table entry is a weight divided by 20; every pair has prior 1/2.

| Fixture | H: AB,A-only,B-only,neither | notH: same ordering | What is witnessed |
|---|---|---|---|
| `reversal` | 5,7,7,1 | 7,1,1,11 | Both marginals 3/5; joint 5/12 < prior. Factors 3/2,3/2,5/7. |
| `oneSided` | 9,7,1,3 | 3,1,5,11 | A=4/5, B=5/9, joint=3/4. Unswapped pooled inequality holds; swapped fails. |
| `unconditional` | 1,2,8,9 | 1,1,6,12 | Mixture A=1/8, B=2/5, AB=1/20, hence unconditional independence. Both individually supportive; joint=1/2 worsens against both. |
| `dependentGrowth` | 8,4,4,4 | 2,4,4,10 | Both marginals=2/3; joint=4/5. Conditional independence fails despite both-sided growth. |

The unconditional fixture supplies a sharper omitted-condition test than merely
observing that unconditional independence differs definitionally from conditional
independence. The dependent-growth fixture shows necessity fails even with all
cells positive and both marginals individually supportive. Common dependence
neither automatically destroys nor guarantees evidential growth; the paired
conditional ratios discriminate it.

Rejected inference: counting supportive reports implies joint support. The
reversal fixture retains supportive marginals but refutes it. Rejected inference:
one pooled conditional inequality implies improvement over both. `oneSided`
retains that condition while reversing the comparison with A. Rejected inference:
unconditional independence supplies the two hypothesis-conditional products.
`unconditional` separates them and defeats the desired corroboration consequence.
The source issue's finite enumerations were discovery only; no exhaustive-search
claim is used as proof.

## What could warrant a dependence assumption?

The mathematical tables answer a consequence question. Applying them requires a
separate, defeasible case about how report receipt is generated. These are
analyst process hypotheses and discriminating tests, not empirical findings:

| Positive process account | Why it could matter | Strongest live defeater and discriminating test |
|---|---|---|
| Common source copied through two channels | A later report can track an earlier source rather than supply a fresh observation; an additional report may repeat the same signal. | Channels might independently check the copied claim. Trace actual acquisition and access, distinguish common wording from common observation, and test what the second channel adds after fixing the first. |
| Separate observation conditioned on adequate hypotheses | Separate acquisition/error mechanisms could support product factorization within each hypothesis. | Separate observers can share a misleading stimulus, latent environment or selection rule. Independence requires an adequate conditioning description and exclusion/control of these dependencies **under each** hypothesis; physical separation alone is insufficient. |
| Coordinated bias or common incentive | Coordination may concentrate matching errors under notH, increasing P(AB|notH) disproportionately. | Shared interests do not establish coordination or numerical strength; independent correction may counteract it. Look for access, communication, stable error patterns and incentives with an actual pathway to reports; compare controls without that pathway. |
| Selection on agreement/report survival | Selecting only agreeing or publishable reports can induce dependence among originally separate channels. | Complete or mechanism-independent sampling may avoid that selection. Reconstruct the inclusion rule and missing/disagreeing channels; distinguish independence before selection from independence in the admitted sample. |

A common-cause graph alone does not deliver the numerical products here without
an explicit probabilistic interpretation and factorization assumptions. Likewise,
absence of a documented link is not a proof of independence. Conditional products
could be warranted approximately rather than exactly, but the present strict
criterion supplies no error margins: if application needs robustness, the next
formal test is a bounded perturbation theorem with explicit lower margins and
cell bounds. Neither adding a latent variable nor collecting more reports is an
automatic warrant upgrade: the residual conditional error process and inclusion
rule remain to be checked. A credible process account can support a dependence
assessment without licensing a particular numerical calibration.

## Overall provisional judgment (2026-11-11)

On the stipulated positive binary model, the paired criterion is the exact
standard for strict both-sided posterior improvement. It is preferable to a
single-sided criterion **for that mathematical question** because the theorem
provides necessity and sufficiency and the retained positive countermodel defeats
the single-sided replacement. Both-hypothesis conditional independence is one
sufficient route, not necessary, and unconditional independence does not supply
it. This judgment rests on the same probability policy and binary hypothesis
interpretation across all results; the cases are not independent empirical
support. The process evidence available here is insufficient to select actual
likelihoods or defend an actual witness-independence claim. Calibration,
truth-conduciveness, access to the relevant process facts, and a norm licensing
belief revision remain distinct unresolved bridges to #934/#931. No universally
binding Bayesian standard or religious conclusion follows.

Strongest standing rival to an applied inference: individually reliable-looking
reports share a hypothesis-dependent error or selection mechanism, so marginal
success does not fix the conditional ratios. Its positive replacement is the
common-source/coordinated-error/selection model above, not bare skepticism. Its
price is an independently warranted account of that mechanism and its bearing on
the selected reports; the table proves logical availability, not actuality. The
positive separate-acquisition rival likewise needs evidence that the conditioning
hypotheses account for relevant shared causes and sample selection. Neither
rival is dismissed because it is unusual, and no actual process is selected.

Revise the mathematical judgment only for a defective proof/encoding or a changed
scope (degenerate cells, more hypotheses, approximate inequalities, different
support sense). Strengthen or reverse an **applied** judgment with independent
process/calibration evidence that discriminates the conditional ratios; suspend
it when unmodelled selection/shared causes invalidate the chosen description.
The historical Atkinson/Peijnenburg preprint and possible later corrections are
navigation from #1396 only: no new historical error attribution is made, no draft
or correction-version evidence has been inspected in this logic task.

## Verification, service experiment and remaining work

Canonical source is the isolated `truth-core-testimony1396` clone. The coordinator
preview is clean e02bd650c2f31160dd1f965b439b1c185cdb421c at
http://127.0.0.1:8879, session `continuation-1111`, path
`Scratch/testimony1396/Edit.lean`, shared lease `/tmp/truth-core-lean.lock`.
`agent_lean.py` accepts full-file in-memory edits; combined vocabulary/proof text
avoids importing a new module absent from the preview. Initial vocabulary response
had no diagnostics (hash e319411fa21383f9a9fd4786b917c60f2efeed4b1e37ada83fabab5f3a5bcc94).
Repeated proof edits found genuine field-rewrite/denominator and theorem-name
errors rather than concealing them. Final combined-source response v5 had no diagnostics, content hash
`9b8b8e83799efe8575b0fb660bfde8781f3de250ecd7f4b1f3e6a96c837017c2`,
service elaboration 0.809s / client total 0.914s. Corpus record lookup returned
the same clean preview identity and record hash
`df0d4d043e7728622b493ebb5d3e42cbcdfbc8451648276cc8e4f8834b091500`.
The initial vocabulary elaboration took 6.041s; the repeated session reused
imports. This is one task, not a throughput comparison. Canonical focused CLI
build of the final four-table Solution passed. The CLI builds actual modules;
the service instead required combined temporary source because new imports
were absent from the immutable preview. Retain the service for repeated
local diagnostics, with that setup limitation and final CLI/CI certification.
Reproduction: `python3 scripts/worker_env.py -- lake build
TruthCore.Results.Logic.CorrelatedTestimony1396.Solution`; service submission
uses `python3 scripts/agent_lean.py FULL-TEXT --url http://127.0.0.1:8879
--workspace /home/brantner/privat/truth-core --session continuation-1111
--path Scratch/testimony1396/Edit.lean --lock /tmp/truth-core-lean.lock
--expect-head e02bd650c2f31160dd1f965b439b1c185cdb421c`. Interactive checks do not substitute for frozen binding,
axiom, Comparator, NanoDa or final delivered-head CI.

The paired question and omission controls are resolved under the declared
assumptions. An actual dependence judgment is blocked by the absence of a
specified nonhistorical report process and independently established acquisition,
error and selection evidence. The next discriminating **application** step is to
select such a process and test its two conditional dependence accounts; the next
formal extension, if needed by that process, is quantitative robustness rather
than additional enumerated tables. Root-facing bridge remains unbuilt and no
root change is expected; use the computed frontier delta, not this expectation,
in the PR.

Claim/type self-sweep: every universal claim is restricted to Reports (positive
cells, normalized rows, non-dogmatic prior); the individual-growth assumptions
appear in IndependenceSuffices; one-sided and swapped criteria are kept distinct.
All countermodels preserve the same hypothesis/report domains and balanced prior.
Process accounts are explicit hypotheses, not read into the table. Historical
attribution is deferred, and no source/claim records were added. Verification
status and actual frontier delta belong to the PR evidence.

## Concrete process test: Comparator and NanoDa on this criterion

This follow-up is a bounded reading of the existing successful verification path,
not a new verifier audit or an empirical error-rate experiment. Evidence revision:
`54bc81bde5420e9153da6709b4965bf7661af45f`; delivered result
[`1239fd26-9a00-4f5c-9090-4b760e2db81d`](../../corpus/results/1239fd26-9a00-4f5c-9090-4b760e2db81d.json),
[configuration](../../results/1239fd26-9a00-4f5c-9090-4b760e2db81d/comparator.json).
The coordinator supplied this nonhistorical application after the mathematical
checkpoint. No gates were rerun, inputs changed or failures injected for it.

### What the reports actually assert

The existing successful criterion log used for PR #1423 contains, in order:

```text
Building TruthCore.Results.Logic.CorrelatedTestimony1396.Challenge
Build completed successfully (894 jobs).
Building TruthCore.Results.Logic.CorrelatedTestimony1396.Solution
Build completed successfully (894 jobs).
Running nanoda kernel on solution
nanoda kernel accepts the solution
Your solution is okay!
```

The complete original local log is `/tmp/testimony1396-verify-criterion.txt`;
this bounded excerpt is persisted here so the process finding does not depend on
temporary evidence alone. The log reports successful builds (which can reuse
unchanged outputs), not two fresh recompilations. It also contains expected
Challenge `sorry` warnings; those are frozen obligations, not proof admissions
in the checked Solution. The prior binding output was `bind-check: 3 bound,
0 pinned, 0 mismatch`, covering this result and the two other #1396 results.
These observations reuse existing evidence, not a fresh claim of final-head CI.

| Observation/component | Actual target and operation | What it does not assert |
|---|---|---|
| Successful Lean Solution build | The configured Solution module is accepted by the Lean build path; its proof is checked in the pinned Lean environment. Lake may reuse valid traced artifacts. | Natural-language interpretation, corpus record identity or empirical report calibration. |
| Comparator's internal export comparison | The selected theorem's canonical name, kind, universe parameters and type agree between Challenge and Solution; the traversed statement environment and designated primitives/axioms agree. It separately traverses the Solution proof dependencies to reject unpermitted axioms. | The Comparator's Rust comparison is not a second proof-typechecking kernel; it does not itself derive the theorem or interpret the prose. |
| `nanoda kernel accepts the solution` | After a successful external command, the wrapper prints this line. NanoDa parses the exact Solution export string already inspected by Comparator and checks all declarations in that export, including proof-term type inference and equality to the advertised declaration type. | NanoDa is not separately given the Challenge or corpus argument/prose and does not perform Comparator's Challenge/Solution identity comparison. |
| `Your solution is okay!` | The overall Comparator pipeline has completed its builds, export comparisons, axiom check **and configured NanoDa call**. | An additional observer independent of the NanoDa result, or categorical/source/interpretation warrant. |
| Existing binding result | The corpus argument's premise/conclusion declarations match the elaborated theorem's binder/result description under the repository binding rules, with sense checks. | Semantic fidelity of a definition or prose, nor a second independent theorem proof. |

Code locators at the evidence revision:
[statement and environment comparison](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L672),
[axiom traversal](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L801),
[build/export path](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L907),
[shared export and NanoDa configuration](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L942),
[ordered final pipeline](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L1012),
[exit-status handling](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/verifier/src/main.rs#L818),
[binding extraction](../../scripts/BindTypes.lean) and
[binding comparison](https://github.com/moritzbrantner/truth-core/blob/54bc81bde5420e9153da6709b4965bf7661af45f/scripts/corpus.py#L4281).

The pinned NanoDa source was read locally at
`6ae1f0cd962f081f6c423454c5da729d841236a7`:
[`main.rs`, `use_config`](https://github.com/ammkrn/nanoda_lib/blob/6ae1f0cd962f081f6c423454c5da729d841236a7/src/main.rs#L22)
calls `check_all_declars`;
[`tc.rs`, `check_declar`](https://github.com/ammkrn/nanoda_lib/blob/6ae1f0cd962f081f6c423454c5da729d841236a7/src/tc.rs#L81)
infers the type of a theorem/definition/opaque value and asserts definitional
equality with its declaration type; the parser rejects unpermitted axioms when
`unpermitted_axiom_hard_error` is true. This supports implementation-level
separation from Lean's kernel, without claiming a global correctness audit of
either kernel. The exporter entry point was read locally at
`5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`, `Main.lean`: it imports the
requested module environment and dumps the requested constants. The repository
pins Lean to `leanprover/lean4:v4.35.0` and builds the matching exporter tag;
[pins](../../scripts/verifier-pins.env), [wrapper](../../scripts/verify-result.sh)
and [axiom policy](../axiom-policy.md) identify this setup. These are actual
local code observations, not newly fetched source claims.

### Shared acquisition and different checks

Both outputs depend on the same selected result/configuration, theorem name
`TruthCore.Results.Logic.CorrelatedTestimony1396.criterion`, Solution/vocabulary
and imported Lean/Mathlib declarations, compiled artifacts, machine, orchestration
and selected successful run. Comparator parses one `solution_export` and sends
that **same string** to NanoDa, writing it to a temporary `solution.ndjson`.
Consequently, another export of a different statement is not an independent
observation of the intended source statement merely because two consumers accept
it. Exporter/artifact fidelity, run/revision identity and the chosen statement
remain shared acquisition obligations. No such defect was demonstrated here.

The selected config permits `propext`, `Classical.choice`, `Quot.sound` and enables
NanoDa. The Rust proof-closure axiom traversal is the result-policy authority;
NanoDa receives the same permitted list with hard errors on unpermitted axioms,
plus native natural/string extensions. The general wrapper adds `propext` for
exported-prelude reconstruction when absent; **this selected config already
contains it**, so that adjustment changes no axiom allowance here. NanoDa is a
distinct typechecking implementation from Lean, but neither implementation
independently warrants the chosen mathematical axioms or natural-language
interpretation. Different algorithms can share a specification, assumptions,
export representation, selection and implementation defects; observed separate
executables establish none of their statistical error distributions.

The strongest positive reason to retain both is complementary obligation coverage
and implementation diversity. A proof of the wrong frozen statement need not
pass the identity/environment comparison. A hypothetical proof-term acceptance
mistake specific to Lean could be rejected by NanoDa when faithfully exported;
a mistake specific to the Rust comparison need not occur in either kernel.
Conversely, NanoDa acceptance alone supplies no comparison to the Challenge,
and equality to the Challenge alone supplies no second kernel proof check.
These are conditional reasons grounded in different checks, not demonstrated
fault injections or calibrated rates. Shared input does not make the additional
kernel check useless: checking the *same intended proof* by another implementation
is its purpose. It also does not make the two reports statistically independent.
Required gates retain their existing roles and remain required.

### Does the generic two-report model apply?

Not directly to the two success messages as interchangeable, independent witness
reports. First fix H:

- H = validity of the exported proof under the selected formal background:
  Lean and NanoDa address a common formal target, conditional on faithful export
  and artifact identity. Comparator's internal equality/axiom checks address
  additional obligations, rather than repeating that proof check.
- H = identity with the frozen intended formal statement: Comparator addresses
  the Challenge relation; NanoDa alone has no Challenge input. It can check a
  valid proof of a different statement without settling that identity.
- H = faithful expression of the philosophical/prose claim, or warranted belief
  in it: neither acceptance message checks that interpretation. Existing binding
  helps track which encoded statement was checked; it does not cross this gap.

These are coexisting targets with different roles, not competing metaphysical
options. An overall engineering assurance claim can explicitly conjoin formal
validity, frozen identity, input/revision fidelity and semantic fidelity; passing
the first checks does not silently supply the remaining conjuncts.

There is a further observable nesting: let A be successful completion of this
configured Comparator pipeline and B be its NanoDa-acceptance event. Under this
unmodified control flow, A requires B; the final Comparator success message is
printed only after the external kernel call returns successfully. Therefore the
A-without-B cell is structurally excluded for those event meanings. The #1396
`Reports` theorem requires **all four cells strictly positive within each
hypothesis**, so this literal message pair does not instantiate that theorem.
This is an event-definition mismatch, not a calculated negative Bayes factor.
If instead A denotes internal comparison success before the kernel call, NanoDa
is invoked only after that comparison and axiom checking pass: the observed
NanoDa sample is selected by earlier gates. A population of possible failures,
both-hypothesis calibration and an explicit observation/sampling policy would
still be needed to assert statistical conditional independence. No such
population, frequencies or probabilities are supplied by this successful log.

### Provisional process assessment and reassessment

The actual code supports complementary deductive assurance and distinct kernel
implementations; it does **not** support a claim that Comparator and NanoDa are
two statistically conditionally independent favorable witnesses concerning a
single undifferentiated H. The final Comparator report includes the NanoDa stage,
and its internal identity check has a different target from kernel validity.
This discriminates the live process question without new probability assignments
or another theorem. It is not an assertion that their errors are correlated to
any specified degree, that one checker is redundant, or that required gates can
be weakened. The evidence supports using both for their explicit obligations.

Strongest positive rival: independent implementations could reduce exposure to
implementation-specific proof-checking mistakes. This survives as a qualitative,
conditional engineering reason. Its stronger statistical version owes an explicit
error population, acquisition/selection policy and separate calibration under
validity and invalidity, none available in this reading. Strongest adverse rival:
a shared exporter/artifact/statement error can leave both checks apparently
successful about a different formal object, while a shared mistranslation remains
outside both. Its price is evidence of that actual defect; no defect is inferred
from the availability of the failure pathway. Separate binding and semantic
review target parts of these gaps rather than magically remove all shared trust.

Revision conditions: change this assessment if the orchestration, export path,
config or event definitions change; if a specified error population supplies
relevant calibration; or if concrete evidence demonstrates a failure of one
checking/input/semantic obligation. The present bounded applicability test is
resolved: literal success messages cannot inherit the positive four-cell theorem,
and algorithmic diversity supplies no statistical-independence certificate.
A probabilistic application remains blocked by event/population/calibration and
policy-to-warrant gaps. The useful continuation is to keep the explicit layered
assurance claim when reporting these results and investigate a **concrete alleged
mismatch**, if one arises, against its own layer. A speculative global verifier
audit, numerical fault estimates, extra tables and automatic robustness work are
not warranted by this finding. The #934 epistemic bridge and every probabilistic
root application remain UNBUILT; historical stages 4–6 remain excluded.
