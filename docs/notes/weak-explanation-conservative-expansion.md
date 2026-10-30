# What weak explanatory coverage actually adds

This #312/#319 investigation asks whether the current existence-reason clauses
can connect an existence explanation to efficient causation or conserving
dependence. It first reuses the existing definitions and finite results. The new
finding is a **general conservative model expansion**, rather than another
isolated countermodel. No adequate metaphysical explanation is thereby supplied
or refuted, and no root premise is discharged.

## Arena and exact reuse

The fixed arena is `CosmologicalInference.Ontic`: one candidate domain, one
world type and accessibility relation, world-relative existence and a separate
world-local causal relation. `ExistencePSR.Model` adds candidate reason tokens
and tagged existence facts. Its `Sound` condition is only factivity of the
explanandum, and its `ExistencePSR` condition is token coverage of existing
individuals. `Reason.intrinsic x` is explicitly not evidence that an essence
really explains its instantiation.

`WorldwiseExplanation.StableExplanation` asks for one rigid reason token
wherever the same individual exists. `ReasonInvariant` preserves an explaining
link only **if its target exists at the destination world**. These two clauses
must not be read as unconditional persistence of an explanation into every
world, nor as the independent modal sufficiency condition
`BruteFoundationExplanations.NecessitatesExistenceAt`.

The earlier exact results remain useful:

- `WorldwiseExplanation.worldwise_and_invariance_implies_stable` gives token
  stability from worldwise coverage, an existence witness and guarded invariance.
  Its `worldwiseWithoutStable` control defeats the bare quantifier shift.
- `BruteFoundationExplanations.necessaryReasonAndNecessitation` and
  `contingentExcludesNecessaryNecessitatingReason` isolate the added
  **necessitation** condition. `abstractReasonCoverageInsufficient` already
  distinguishes sound local coverage from a necessary concrete bearer.
- `PowerExistenceBoundary.powerExistenceBoundary` already separates exercised
  unborrowed power, support of esse, necessity and proper-part composition.
  `originalPowerBlocksEsseSupportIfItTransmits` adds the explicit condition
  that a conserver transmits **this same power**. Finite power grounding alone
  does not give that condition.
- `RegressDomains.ExplanatoryDependence` separately supplies `requires`, and
  `ExplanationTransfer` separately needs a well-founded rank decreasing across
  every admitted explanatory requirement. Neither datum is supplied by PSR
  token coverage.
- `UnderivedCommonSource.ActualCauseSupportsEsse` is the opposite-direction
  actual-cause-to-selected-support interface. It is not an equality of causes,
  grounding, explanatory tokens or power transmission.

No existing general expansion of every `Ontic` interpretation was found in this
inventory. The existing finite witnesses do not establish that universal
model-expansion claim by themselves.

## Construction and checked target

`ConservativeReasonExpansion.canonical o` keeps `o` literally unchanged and sets

```text
explains(w, r, fact(x))  iff  r = intrinsic(x) and ExistsAt(w,x).
```

`CoverageAndGuardedStability` merely bundles the four existing weak clauses.
`canonicalCoverage` constructs them for any ontology, including any original
causal relation or existence pattern. It selects no real essence and introduces
no additional existent reason-bearer.

`onticPropertyConservative` makes the consequence precise. For any property `P`
of the original `Ontic` signature, universal validity of `P` over enriched models
with these weak clauses is equivalent to universal validity of `P` over the
original ontologies. The forward proof expands an arbitrary ontology; the
reverse proof projects it. The quantified property is a model-theoretic
parameter, not an opaque philosophical premise claiming the desired conclusion.

Thus these clauses alone prune **no** family defined solely by the original
frame, existence and causal data. This does not say that an adequately
interpreted PSR is empty or false. An independent adequacy, real-ground or
cause-correspondence condition could restrict the expansions; the present
construction makes no claim to satisfy such a condition. Grounding and
temporal conservation are not fields of `Ontic` at all, so a statement about
those relations requires its own interpretation and coherence conditions.

### Same-model controls and nonvacuity

The certificate reuses named ontologies without modifying any of their fields.

1. On `NecessaryVariableEffects.fixedEffects`, the source and selected effect
   actually exist and are both necessary on the universal Bool frame. The
   existing sound distinct causal edge remains. The selected effect nevertheless
   receives a weak intrinsic-tag explanation with guarded token stability.
   This is a joint logical control against treating such a tag or modal
   necessity as the absence of a distinct cause. It is not a genuinely adequate
   intrinsic-reason counterexample to Aquinas.
2. On `alternatingEffects`, the selected effect exists at the first world and
   is absent at the second. Weak coverage, token stability and guarded
   invariance still hold. Its actual intrinsic-tag explanation does not persist
   to the absent-target world. This exhibits the guard's importance; a stronger
   unconditionally invariant explaining relation would conflict with factivity
   and this absence.

The controls have actual distinct causal relata and nonempty world/candidate
carriers. Their conclusion types expose actual existence, modal status and
causal soundness. They do not infer actuality from an inhabited carrier, nor
rely on a root with no accessible worlds. The general expansion permits empty
world or candidate types, but supplies no actual existence from those cases.

## Conservation reading and stronger rival accounts

The existing `AQUINAS-ST-I-Q104-A1-EN` witness was materialized and its entire
article read, including objections and replies. The existing translated claims
`STMT-BECOMING-CAUSE-NEED-NOT-SUSTAIN-BEING` and
`STMT-DIVINE-ESSE-CONSERVATION-CONTINUES-GIVING-ESSE` already preserve the relevant
distinction: a builder's completed action is not the same causal role as a
direct giver of esse; accidental removal of corruption is another role again.
Reply 4 characterizes divine conservation as continuing the esse-giving action,
without a new motion or temporal production at each instant. No new historical
claim is added here, and the historical physical examples are not adopted as
modern scientific premises.

The strongest remaining accounts must answer the same questions:

| Account | Positive commitment | Still-needed bridge |
| --- | --- | --- |
| Efficient giver/conserver of esse | The being of an effect depends on a direct cause in the specified esse sense, distinct from completed production or anti-corruption preservation. | Defend the actual case, its continuing dependence and its interpretation into `CausesIn`/the world-local causal edge; a token label does not supply it. |
| Intrinsic/noncausal reason | A real nature or necessary structure is proposed to make an existence fact intelligible. | Defend that reason's reality and sufficiency, including why the nature is instantiated; `intrinsic` tags and guarded stability do not do so. |
| Whole-first/global grounding | The fundamental whole or global structure explains dependent members without a parts-first efficient-cause story. | Defend real grounding and its direction/scope. A chosen fact-ground edge is not automatically an efficient cause or a conserver. |
| Brute/global-fact permissiveness | Some existence or global arrangement is accepted without an ultimate reason; local dependencies may still be explained. | Defend the principled restriction of the explanatory demand. It is not refuted by assigning previously unexplained facts tokens in this weak model. |

The source-backed conservation candidate remains
`AQUINAS-ETERNITY-EXTERNAL-DEPENDENCE`. Its obligation B requires a defended
interpretation of a distinct direct conserver into the relevant cause of esse.
The expansion theorem supplies neither this interpretation nor its converse.
The existing `docs/eternity-dependence-connection.md` and the shared vocabulary
owner's inventory remain authoritative for the other obligations.

## Premise comparison and verification boundary

Intended and actual root-path premise change: **none**. All previous open
premises are retained, with none added or discharged. The new premise-free
certificate establishes a model-class boundary, not the truth of any PSR,
efficient-cause principle, conservation account or interpretation of nature.
No new source claim or cross-domain identification is introduced.

The frozen Challenge hash is
`4e6de2f04501b88c699be4d23e54f39146c67138477e42cf1a259759f7cead25`.
The coordinator-owned service accepted the combined canonical definition and
solution at preview revision `f2544a0142304bf074112e7323cb5b8ab6e46840`, path
`Scratch/dependence/ConservativeReasonExpansion.lean`, content SHA256
`af168d06e02183d3c390989daa35af1d786ad501ddf17b5b6998b9d58472c846`.
It reported no errors and `checks` depends on no axioms. This is focused Lean
development evidence; delivered-head CI supplies required build, binding,
Comparator and independent NanoDa verification without duplicate local runs.
