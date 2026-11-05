# Carneades population aggregation: finite arithmetic boundary

Owner-authorized consequentialism lane, baseline `8bf7290b`, separate from
root-frontier closure. This is a research note and independent mathematical
test, not an attributed Parfit claim or certified historical reading.

## Reading and source boundary

Read the complete English `en-orig` public auto-caption stream of **Derek
Parfit’s Repugnant Conclusion (Population Ethics)**, Carneades.org channel,
https://www.youtube.com/watch?v=zG814I1DBzU (09:04 duration), including the
closing discussion and nonargument outro. Audio/slides remain unchecked;
caption misspellings of Parfit warn against treating this as authoritative
wording. Speaker is only the channel narrator, not an identified person.
Reproduction uses the installed downloader, with no login, payment or new
dependency:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-population.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=zG814I1DBzU'
```

Downloaded VTT SHA256: `3b06fbdf3920a7d1b9454a590ea4c19800a34501322276346f2994fa2b3ad8b2`. It identifies the read
caption download, not a corpus `span_sha256`. No `media_span` export provenance,
materialization or audio fidelity check was completed, so there is no new
source/passages/claims record. A future attributed claim must first meet those
requirements. The formal control is independently stipulated mathematical
arithmetic; its truth does not depend on these captions being accurate.

- **00:31–02:19:** the narrator introduces an impersonal total principle and
  says a sufficiently large low-positive-average population can rank above a
  small high-average one. The desirability bridge is presented, not justified;
  the video explicitly points elsewhere for justification.
- **02:25–03:24:** bar height means average welfare and width population count;
  their product is total. **02:44–02:54** explicitly permits individuals above
  and below the mean. The mathematical control preserves this summary scope.
- **03:34–04:46:** add an equally sized population of lower but positive average
  quality; the narrator gives totals four and six. The precise numerical labels
  of pictured populations are not authenticated without the slides.
- **04:51–06:41:** grouping the same population differently preserves total;
  doubling count while lowering the mean from four to three increases total.
  This does not prove that redistributing welfare among actual individuals is
  harmless; grouping and redistribution are distinct operations.
- **06:43–07:52:** iterate toward large populations with very small positive
  mean and total exceeding the baseline. **06:54–07:09** even permits negative
  individual lives. Therefore an attribution that *every* final life is barely
  positive is stronger than this caption evidence. Our profile constrains only
  the mean. No finite sequence limiting argument is imported from the rhetoric.
- **07:56–08:19:** the narrator asks what could replace the total principle and
  avoid unfairness, promising later replies. The video does not defend average
  ranking; that rival is our independent mathematical comparison.

## Constraint, strongest rival and rejected approaches

`Profile` is a nonempty finite Nat count with a real mean, on one stipulated
cardinal interpersonal scale; `total = count * mean`. For **each** strictly
positive epsilon below a given finite profile’s mean, Mathlib `exists_nat_gt`
chooses a finite count exceeding both the original count and total/epsilon.
Positive multiplication gives strictly greater total at exactly epsilon mean.
Thus every arbitrarily small *fixed positive* mean has a finite witness. No
infinite population, infinite total, limiting population, maximum, physical
availability or per-person welfare assignment is asserted.

The strongest encoded rival is average ranking: on the same two profiles it
strictly prefers the high-mean baseline, while total ranking strictly prefers
the large low-mean one. A count-one mean-two baseline and epsilon one suffice
to refute the existence of one strict relation agreeing with both policies on
all profiles. The theorem forces disagreement; it does not choose the true
policy. Equal positive counts recover equivalence of comparisons, and zero
mean cannot beat positive total. These controls identify count variation and
strict positivity as consequential guards, rather than treating total/average
as uniformly interchangeable or extrapolating the construction to zero.

Rejected: ordinal preferences supply a common cardinal interpersonal scale;
positive mean implies all lives positive; the narrator’s regrouping is a proof
of distributional indifference; the arithmetic definition makes maximizing
morally right; total welfare alone specifies every consequentialist theory;
average ranking is thereby normatively established; arbitrarily large finite
profiles imply actual feasible population expansion; an unrestricted objective
has an attained maximum. Act/rule, rights, demandingness, and stochastic
choice require further semantics and are not silently collapsed into this
bounded comparison. Existing Railton welfare/rightness records deliberately
use nonnumeric predicates and are not falsely reused as an aggregation axiom.

## Verification and remaining obligations

Frozen Challenge SHA256:
`58fa4570d5065f44160d25b0a160c46d578e7f06011ddc09a42776daa1724c9c`.
The exact `controls : Controls` theorem has no top-level premises; its universal
positive-epsilon and same-count clauses retain their explicit local guards.
This is derived arithmetic, not an opaque bridge transcription.

A serialized warm-service request to `/lean/diagnostics`, coordinator workspace
`/home/brantner/privat/truth-core-sprint-proof`, head
`49b4589aa6744c91a6bc9adec13215d0e7245c9d`, existing session `causal-harvest`,
virtual path `Scratch/carneades-consequentialism/Population.lean`, version 3,
accepted the combined declaration and proof without errors/warnings. Exact
content SHA256:
`1d433dba925ec6bf9cba5cdc7ac9e4b28de166a2e81058d3a4be2344a5653fa7`.
Axiom print reported exactly `propext`, `Classical.choice`, `Quot.sound`, within
the approved Mathlib profile. Initial preview failures were import placement
and using an obsolete multiplication-cancellation theorem name, corrected
without changing the frozen Challenge. The shared service was not restarted
and its checkout/session was not mutated by this worker. Interactive checking
is development evidence, not canonical binding/Comparator/NanoDa certification;
final delivered CI owns those gates.

No source-derived premise is established. Actual welfare commensurability,
interpersonal aggregation, availability of arbitrary finite profiles and the
normative authority of either ranking remain OPEN for ethical application.
Intended and actual root-premise delta: zero. The new independent statement is
not connected to a root argument and closes no existing frontier leaf.

## Individual scoring and replication obstruction (#1038)

The new `PopulationScoring.Population = List ℝ` assigns an explicit welfare to
one individual per entry. Count is list length, ordinary total is the sum and
mean is total/count. For a strictly positive count, `summary` reuses the old
`PopulationAggregation.Profile`, and `summary_total` proves its product total
equals the individual sum. The old summary theorem has not become a distribution
theorem by relabeling: `replication` imports and consumes the exact existing
`TruthCore.Results.Ethics.PopulationAggregation.controls`, then realizes its
finite count by `List.replicate`. In the generic score proof the old real-number
inequality is instantiated on **score units**, not by identifying f(w) with
welfare w; the new list contains welfare w at each entry and its score is
n*f(w). All entries in that replication equal the specified welfare. The common interpersonal cardinal scale remains stipulated.

The proposed population value `value` is independently constrained by
`Additive f value`: on **every** finite list it equals the sum of a real-valued
per-person score `f`. For any welfare `w` with `f w > 0` and any finite baseline,
sufficiently many replicas strictly exceed its value. The baseline can be empty
or mixed-sign; it need not have positive welfare or score. No monotonicity,
continuity, linearity of f, or normalization of f at zero is assumed. If every
positive welfare has positive score, then for each cutoff δ>0 the construction
chooses w=δ/2 and a finite nonempty replication outranking the baseline.

`NoLowReplication value p δ` explicitly bounds every uniform population with
0<w<δ and every positive finite replication count by the same baseline's
value. For δ>0 this contradicts additive representation and universal
positive-life scoring. Thus at least one member of **this particular bundle**
must be rejected. This is neither an unrestricted population-ethics impossibility
nor an argument choosing one uniquely correct ranking. The arithmetic assumes
all finite lists are admissible comparisons; physical feasibility, available
resources, identity and welfare-measurement adequacy remain OPEN.

The omission controls distinguish consequential alternatives:

- Zero scoring preserves additive representation and the no-low-replication
  bound but rejects positive scoring of positive lives.
- Average welfare preserves the bound below a nonempty positive-mean baseline.
  No f represents average as an additive sum on all finite lists: [2] and [2,2]
  already force incompatible per-person scores. It therefore rejects additive
  representation. Adding any life with 0<w<the baseline's mean strictly lowers
  its average while strictly increasing ordinary total. The original list must
  be nonempty; its positive mean follows from this exact positive-lower-life
  guard rather than from an assumption that each existing life is positive.
- Positive-critical-level scoring sums w-c. For c>0 it bounds replications with
  0<w<c below baseline [c+1], but rejects universal positive-life scoring:
  c/2 has negative score. Adding **any** positive life below c strictly lowers
  critical value, whatever the existing distribution. This is its specific
  mere-addition cost; the life remains positive in ordinary welfare units.
- With a finite count cap N and N*w≤the baseline total, every n≤N replication
  has total at most that baseline. Restricting admissible replication can block
  the unrestricted construction without changing ordinary positive welfare
  scores. This is a sufficient cap control, not a claim that every feasible cap
  avoids all ranking reversals.

All-positive [1,1] and mixed-sign [-1,3] both have total two and mean one; the
latter explicitly contains a negative life. Uniform replications have mean
exactly w under n>0. These distribution controls reject the stronger reading
that a positive average implies every life positive, or that summary equality
establishes distributional fairness. List ordering adds no moral significance:
all additive scores sum the same individual entries; no cardinal scale is
inferred from ordinal preference.

The new argument is an analyst formulation with attribution deferred. The
existing source leads and provisional findings above are preserved; no new
source, passage or claim record is added. It is a non-transcription mathematical
constraint, using the old checked theorem rather than a fresh assumed bridge.
Actual premise comparison: no top-level corpus premises, all scoring/cutoff/
nonempty guards explicit inside `Controls`; no root-route premise retained,
added, removed or discharged. Root-frontier delta is zero.

Development service probes used the coordinator's unchanged preview HEAD
`a2d97ecf1429e86b3e12f15b91b735f85e27822e`, session `workloop-20261105`,
workspace `/home/moenarch/moritzbrantner/truth-core`. Initial separate-file
submission could not resolve the new vocabulary outside the canonical clone;
a combined full-content submission corrected a nonexistent List import and
then was rejected because the preview's cached PopulationAggregation Solution
predates the module migration. Final combined content SHA256 was
`33dcf69683a7b95fb592adbb8ec5991805800180907f1c39639e7d3979975527`.
This is rejection evidence, not proof verification. The worker did not rebuild
or alter the preview; canonical CLI verification is used instead.

`total_low_replication` explicitly instantiates the generic theorem with
f=id and value=ordinary total. Its premises are only an arbitrary finite list,
a cutoff δ and δ>0; the positive-life-score and additive-representation guards
are proved by their definitions rather than introduced as further assumptions.
Its moral authority and feasible realization remain open as above.

The same service returned the seed dossier with the exact preview HEAD,
workspace and dirty-state binding above; it did not establish a new proposition
or change corpus status. CLI `corpus.py related` and `dossier` supplied reuse
context before implementation. For this task the service did not replace CLI
proof development because of the stale module cache; retain the shared preview
only after the coordinator refreshes its dependencies in a future experiment.

Claim/type self-sweep: the new statement, inference, argument and result all bind
to `PopulationScoring.Controls`. Its representation, strictly-positive score,
cutoff, count and nonempty assumptions remain within the quantified clauses;
there is no unrestricted negative conclusion or premise truth assertion.
`replication` permits any real per-person function but requires positive score
at the selected welfare; `low_replication` separately requires positive scores
for all positive welfare. The zero, average, critical-level and capped controls
remove different hypotheses rather than refute the generic conditional. The
all-positive/mixed example asserts only equal summaries and their displayed
entry signs. No new metaphysical relation or historical attribution is hidden
in the definitions. The existing source findings and old summary theorem retain
their original, narrower scope.

Canonical verification: the focused build of
`TruthCore.Results.Ethics.PopulationScoring.Solution` passed without warnings;
`corpus.py bind-check --result FINITE-POPULATION-SCORING-TRADEOFFS` reported
one bound result and zero mismatches. `scripts/verify-result.sh
FINITE-POPULATION-SCORING-TRADEOFFS` accepted the frozen Challenge/Solution
type equality and checked the solution with NanoDa, allowing only `propext`,
`Classical.choice`, `Quot.sound`. The Challenge's expected `sorry` is separate
from the real Solution. Offline source manifests, attribution check (no changed
stating claims), corpus, bundle audit and module checks passed. Final delivered
CI retains scoped library NanoDa and integration coverage. The unrelated Science
induction merge changed no Ethics proof input, so its addition did not invalidate
these checks.

New frozen Challenge SHA256:
`2f4a04d2573ddd94f55ffb2da1d507331f64b423dc818beab5a57e5f036e1851`.
Reproduce using `python3 scripts/worker_env.py -- lake build
TruthCore.Results.Ethics.PopulationScoring.Solution`, the scoped binding command
above and `python3 scripts/worker_env.py -- scripts/verify-result.sh
FINITE-POPULATION-SCORING-TRADEOFFS`. Shared conventions resolved at
sourceRevision `625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

## Shared interpersonal calibration burden

[Companions-in-guilt comparison](companions-in-guilt-new-results.md) extends the
fixed-population boundary: generic opposing individual welfare differences allow
independent positive affine changes of each person's unit to reverse total,
average and fixed critical-level comparisons together. Common positive scaling
and guarded Pareto comparisons survive. This isolates a shared measurement
burden; it does not transfer the variable-count replication conclusion to the
rivals, justify an ethical policy, or discharge any root premise.
