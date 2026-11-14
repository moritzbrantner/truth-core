# Preface paradox: interconnected assertions versus isolated errors (#1584)

**Status:** analyst comparison, attribution deferred. Makinson, "The Paradox of
the Preface" (*Analysis* 25, 1965) and Bovens–Olsson, "Coherentism, Reliability
and Bayesian Networks" (*Mind* 109, 2000) are navigation leads, not sourced
claims. Formal home: `TruthCore/Logic/PrefaceConnectivity.lean`, results in
`TruthCore/Results/Logic/PrefaceConnectivity/`, spec
`specs/preface-connectivity-1584.toml`.

**Connection:** a named connection plan to #930/#931/#934 (cumulative warrant,
premise assessment, correction), not an established root route. No root premise
is discharged and no root closure is claimed.

**Boundaries kept from the issue.** Nothing here assigns a probability to any
Truth Core statement, applies `0.99^300` to the corpus's proposition count,
adds a premise that some Truth Core conclusion is false, introduces a
confidence score, or demands wholly independent premises.

## The owner's hypothesis, made testable

The owner observed that a foreign-language word in a coherent paragraph is easy
to spot: surrounding structure makes some local errors detectable. The
hypothesis is comparative: the preface paradox is more forceful for a heap of
disconnected beliefs than for a structured graph whose propositions constrain
and cross-check one another. The question is *which* structural features change
the paradox, not whether connectivity guarantees truth.

## One model for all five tests

`profile κ ν n` is the Mathlib product of a **shared coordinate** (measure κ)
with **n independent local coordinates** (Mathlib `Measure.pi` of one measure ν).
Assertion *i* is true when the shared state lies in `G` *and* local state *i*
lies in `C`. The shared coordinate is a common-mode condition every assertion
relies on (a shared framework, method or source); each local coordinate is an
error opportunity specific to one assertion. A local check raises a flag in a
local event `F`; checks see only local coordinates, so they are blind to the
shared condition by construction. The product's independence is **stipulated**.
Real belief systems can have partial overlaps and chains of dependence that this
two-level model does not cover.

The term *independence* is used in three senses here, recorded in the
disambiguation `ab69cfd0-628d-4925-bc8c-2ea39925b9b8` (`ERROR_DEPENDENCE`):

| Sense | Lean | Meaning |
|---|---|---|
| ERROR_DEPENDENCE_1 | `SharedOnly ν C` (ν C = 1) | every assertion expresses the shared condition; errors are all common-mode |
| ERROR_DEPENDENCE_2 | `IsolatedOnly κ G` (κ G = 1) | the shared condition is certain; errors arise only from independent local coordinates |
| ERROR_DEPENDENCE_3 | `TruthIndependentFlag ν C F` | a check's no-flag event is independent of what it checks: no discriminating information |

Threshold acceptance reuses `ThresholdBelief.Accepted` (t ≤ μ.real A,
PRO_TANTO_SUPPORT_THRESHOLD_FULL_BELIEF_1 from #1063). It is an analyst policy,
not epistemic warrant.

## Compared cases

| Case | P(each assertion) | P(all true) | P(some false) | Makinson tension (t>1/2)? |
|---|---|---|---|---|
| Isolated errors (ERROR_DEPENDENCE_2), local q<1 | q | q^n | 1−q^n | yes for all large n, when t ≤ q |
| Shared only (ERROR_DEPENDENCE_1), shared q | q | q | 1−q | never, at any n |
| Shared g, local p<1 | g·p | g·p^n | 1−g·p^n | yes for all large n, when t ≤ g·p |
| Shared g, local p, perfect local checks, after no flag | g | g | 1−g | never, at any n |
| Shared g, local p, truth-independent checks, after no flag | g·p (general formula with ν(C∩Fᶜ)=p·ν(Fᶜ)) | g·p^n, unchanged | (not certified) | (not certified) |

Every entry not marked "not certified" is a theorem in the stipulated profile
(n ≥ 1; for the q^n < q comparison n ≥ 2 and 0<q<1). The conditioned
per-assertion entries come from the certified formula
P(assertion i | no flag) = κ(G)·ν(C∩Fᶜ)/ν(Fᶜ); in the truth-independent row the
value g·p is that formula after substituting the independence equation, an
algebraic step not separately registered.

## The five tests

**Tests 1–2: isolated versus dependent assertions** (statement
`14173d56-3d40-474f-9aaf-81aa92981f00`, theorem `marginalsUnderdetermineJoint`).
With the same per-assertion probability q, the isolated-error profile gives
q^n < q, while the shared-only profile (the issue's 300 restatements of H) gives
joint q and some-failure 1−q. So per-assertion probabilities do not determine
the joint: `q^n` is a consequence of the stipulated ERROR_DEPENDENCE_2 regime,
not of q and n. The same theorem certifies that conditioning on n ≥ 1 copies of
one evidence event equals conditioning on it once: restating or repeating H adds
no confirmation. The joint probability of n assertions each at probability q
always lies between max(0, 1−n(1−q)) and q: the lower bound is the #1063 support
bound `1 ≤ μ(⋂Aᵢ) + Σ(1−μ(Aᵢ))` (no independence premise), and the upper bound
is measure monotonicity (elementary, not separately registered). The shared
profile reaches the upper end, the isolated profile gives q^n, and the #1063
uniform lottery reaches the lower end (joint 0 at q = 1−1/N). The dependence
structure, not q and n, decides where the joint lies. This is why `0.99^300` must not be applied to a
corpus count: that number assumes ERROR_DEPENDENCE_2, and nothing licenses that
assumption for an interconnected corpus.

**Test 3: contextual cross-check** (statement
`4a85e1e3-c030-46f1-8888-e65d7a042afd`, theorem `crossCheckBoundary`).
Conditioning on no local flag gives

  P(all true | no flag) = κ(G) · (ν(C∩Fᶜ)/ν(Fᶜ))^n ≤ κ(G).

- A *discriminating* check (flags concentrate on local errors) raises the
  per-index factor from ν(C) toward 1. Perfect local detection (`F = Cᶜ`) makes
  the posterior exactly κ(G) for every n: the count-driven local risk is gone.
  Each conditioned assertion also has κ(G), so after perfect checks no
  threshold above one half accepts both an assertion and "at least one is
  false".
  This is the formal content of the foreign-word observation.
- A *non-discriminating* check (ERROR_DEPENDENCE_3) leaves the posterior equal
  to the prior. A check that only re-derives a claim from the same untested
  input, or repeats a common source, is one concrete way to be
  non-discriminating. The #1396 tables give the exact criterion for when two
  correlated reports corroborate; this result adds the many-assertion,
  shared-blind case.
- No number of shared-blind local checks raises joint support above κ(G).
  Interlocking local structure can catch local errors; it cannot certify the
  shared framework it presupposes. Support for G needs evidence that
  discriminates G itself (for G as a binary hypothesis, the #1396 criterion
  applies).

The improvement is measured by the change in the per-index factor, not by a
count of graph edges: an edge whose check is truth-independent changes nothing.

**Test 4: worldview elimination** (statement
`ebf27107-3288-4a10-8d66-1eb68513c464`, theorem `eliminationCoverage`, reusing
`ReflectiveCoherence`). A bundle with no common model (WORLDVIEW_CONSISTENCY_1
fails) is false at every world: a demonstrated W ⊢ ⊥ eliminates that exact
commitment bundle under the stated semantics. To infer that a survivor is true,
the coverage premise "some candidate is true at the actual world" is an explicit
hypothesis. The existing two-world control shows it is needed: one candidate is
inconsistent, the other is the consistent duty-denying worldview, and the
survivor is false at the actual world. A coherent-but-false worldview survives
every consistency test, which is the worldview-level counterpart of the shared
condition being invisible to local checks.

**Test 5: the Makinson boundary** (statement
`74e47e53-eb0b-4963-93c0-254bd1da67b0`, theorem `hierarchicalPrefaceBoundary`).
Makinson's tension needs justification for each assertion *and* for "at least
one is false". In the model:

- Under pure shared dependence (ERROR_DEPENDENCE_1), the two beliefs have
  probabilities x and 1−x, so no threshold above one half accepts both, at any n.
  The shared risk 1−κ(G) remains in full. Dependence removes the count-driven
  tension; it does not remove error.
- With any local error probability (ν(C) < 1), for every threshold t < 1 the
  some-failure event is accepted for all large n, while acceptance of each
  assertion depends only on κ(G)·ν(C), not on n. Dependence on a shared
  condition does not by itself remove the paradox; the number of independent
  local error opportunities drives it.

Common-mode error is the control the issue asked for. It is a real error
source that a large count of assertions does not amplify and local coherence
does not detect.

## What is formal, what is model, what is warrant

- **Formal (Lean, Comparator):** every equation and threshold statement above,
  in the stipulated profile and the fixed `ReflectiveCoherence` semantics. They
  are conditional mathematical facts about these models.
- **Analyst model:** reading the shared coordinate as a framework or source,
  local coordinates as assertion-specific error opportunities, and flags as
  coherence checks. These readings are interpretations, not established
  descriptions of any actual inquiry.
- **Provisional philosophical judgment (2026-11-14):** the owner's comparative
  hypothesis survives in a sharpened form. The preface argument's force depends
  on independent, undetected local error opportunities. Interconnection helps
  when, and to the degree that, it works as *discriminating* local checks. It
  does not help when it is mere restatement or shared-source repetition, and it
  never certifies the shared assumptions themselves. A structured graph
  therefore faces a weaker count-driven preface argument than an atomized list
  *only if* its cross-checks discriminate. Its residual risk then concentrates
  on its shared commitments, where the right response is direct evidence about
  those commitments and the testing of rivals (test 4), not a blanket
  probability discount for size.

  Evidence for this judgment: the five theorems above; #1063 and #1396 as
  reused, not independent, support. Revision conditions: a realistic dependence
  structure (partial overlaps, chained checks) in which discriminating checks
  fail to reduce the count-driven risk; or evidence that a given body of checks
  is truth-independent.

## Strongest standing rival

**Common-mode rival.** Target: the inference from "cross-checked" to "reduced
preface risk". Mechanism: checks share the error they are meant to detect, so
they are ERROR_DEPENDENCE_3 for that error. Independent justification: the
theorem shows that shared-blind checks provide exactly zero support for the
shared condition, and that truth-independent checks provide none at all. This
is a substantive rival with a modeled mechanism, and it applies to every
worldview, theistic or not. Its price: it must show *which* checks in a given
body of inquiry are truth-independent or share the failure. A bare possibility
of shared error is not that showing.

## Remaining gaps and next tests

1. **Partial dependence.** Replace the two-level product with a finite Bayesian
   network (several shared nodes, overlapping supports) and test whether
   discriminating checks still reduce the count-driven risk monotonically.
2. **Imperfect checks with false alarms.** The general formula covers them; a
   threshold statement for when an imperfect checker blocks the Makinson
   tension at all n is not yet certified.
3. **Application.** Whether specific Truth Core cross-checks (Lean consequence,
   bind-check, independent semantic review) are discriminating for a given error
   type is an empirical/process question, open here. Lean checking, for
   example, discriminates formal-consequence errors but is blind to
   formalization-fidelity errors.
4. **Bovens–Olsson.** Their impossibility results for coherence measures concern
   coherence as a truth-conducive *measure*. This note uses no coherence
   measure, so a direct comparison needs their setup reconstructed (attribution
   deferred).
