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
