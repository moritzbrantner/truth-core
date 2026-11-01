# Modal quantifier shifts: initial certified models and elimination rules

2026-10-26; research issues [#462](https://github.com/moritzbrantner/truth-core/issues/462)
and [#465](https://github.com/moritzbrantner/truth-core/issues/465), within the
[120-proposition inventory](modal-ontology-120.md) and the
[configuration-elimination loop](configuration-elimination-loop.md).

**Semantic profile:** classical Lean propositions; a constant candidate-entity
domain with world-relative existence; rigid individual and reason-token
identity; two nonempty worlds `Bool` with universal accessibility. The source
and all causally related individuals must exist where they cause. The PSR
signature is `TruthCore.Explanation.ExistencePSR.Model`; causal models reuse
`TruthCore.German.Kant.CosmologicalInference.Ontic`. Accessibility is **not**
a temporal transition or a causal edge. A finite interpretation proves
*formal satisfiability*, not metaphysical possibility.

## Finding 1: local PSR explanation does not yield one global reason

For a chosen existent `x`, the existing `ExistencePSR` condition has the
following quantifier order (ignoring other individuals):

\[
\forall w\,(ExistsAt(w,x)\Rightarrow\exists r\,Explains(w,r,x)).
\]

The new canonical `STMT-MODAL-EXPLANATION-STABLE` instead requires:

\[
\exists r\,\forall w\,(ExistsAt(w,x)\Rightarrow Explains(w,r,x)).
\]

In `MODEL-PSR-WORLDWISE-ALTERNATING`, the necessary bearer `false` exists
in both worlds and satisfies existence-PSR and explanation soundness. At world
`false`, its sole explanatory reason is `.circumstance false`; at world `true`,
its sole reason is `.circumstance true`. Their inequality gives a checked
countermodel to the shift. The **control** `MODEL-PSR-INTRINSIC` also satisfies
existence-PSR but has a single `.intrinsic false` reason across worlds, so both
stability branches are formally inhabited.

Lean results in `TruthCore/Modal/WorldwiseExplanation.lean`:

- `alternatingPSR`, `alternatingNecessary`, `alternatingNotStable`,
  `worldwiseWithoutStable`: closed finite countermodel.
- `intrinsicModelHasStableReason`: positive control reusing the pre-existing
  intrinsic-reason interpretation.
- `stable_implies_worldwise`: general valid direction.
- `worldwise_and_invariance_implies_stable`: conditional converse, **requiring**
  both an existence witness and invariance of the same reason across worlds.
- `disjoint_reasons_preclude_stable`: reusable incompatibility rule when an
  actually existing individual's two worlds admit disjoint reason tokens.

None proves an intrinsic reason is metaphysically adequate. A reason is only
a tagged candidate assigned by the model; `Sound` verifies its explanandum
exists, not that the explanation is sufficient. The open work is to formulate
and defend a principled constraint on what counts as an adequate, invariant
explanation instead of smuggling one into `ExistencePSR`.

## Finding 2: causing something necessarily does not fix what is caused

The following distinct propositions use the same rigid source `x` and
world-relative causal relation:

\[
\forall v\,(R(w,v)\Rightarrow\exists y\,Causes(v,x,y))
\]

and

\[
\exists y\,\forall v\,(R(w,v)\Rightarrow Causes(v,x,y)).
\]

They are respectively `STMT-MODAL-NECESSARY-CAUSES-SOMETHING` and
`STMT-MODAL-SAME-NECESSARY-EFFECT`.

The two models reuse the same two accessible worlds, three rigid candidate
beings (`none`, `some false`, `some true`), necessary particular source `none`,
and the coherent, distinct, existing-endpoint constraint
`STMT-MODAL-SOUND-DISTINCT-CAUSES`:

| Registered model | World `false` effect | World `true` effect | Some effect at each world | Same particular effect at each world | Is `some false` contingent? |
| --- | --- | --- | --- | --- | --- |
| `MODEL-MODAL-VARIABLE-EFFECTS` | `some false` | `some true` | Yes | **No** | Yes |
| `MODEL-MODAL-FIXED-EFFECT` | `some false` | `some false` | Yes | **Yes** | No |

Both models satisfy the same necessary-source condition and the same
all-world causal-exercise condition. The difference is in the **particular
effect**, not whether the source exists or causes anything.

Lean results in `TruthCore/Modal/NecessaryVariableEffects.lean`:

- `necessarySourceVariableEffects`: closed witness with a necessary source,
  an effect at every world, a contingent first effect and **no fixed effect**.
- `fixedSameNecessaryEffect`, `fixedEffectNotContingent`: contrasting fixed
  effect interpretation.
- `same_effect_implies_something`: the valid implication from fixed to
  worldwise effects.
- `disjoint_effects_preclude_fixed`: reusable incompatibility rule: two
  accessible worlds with disjoint effect sets exclude a single fixed effect.

This separates *necessity of exercising causation* from *necessity of a
particular effect*, extending the earlier distinction between necessary
existence and contingent causal **activity** in
`TruthCore/Modal/NecessaryContingentActivity.lean`. It does not establish
divine freedom, a principle of sufficient causation, agency, determinism,
creation ex nihilo, or a necessary concrete being in metaphysical reality.

## Configuration comparison and remaining obligations

| Shared premises | Additional configuration | Lean result | Philosophical status |
| --- | --- | --- | --- |
| Necessary bearer, existence-PSR, soundness | Stable reason | Witnessed by intrinsic control | Adequacy of intrinsic reason open |
| Necessary bearer, existence-PSR, soundness | No stable reason | Witnessed by alternating reasons | Real adequacy/invariance open |
| Necessary source, sound distinct causes, always some effect | Same particular effect | Witnessed by fixed-effects control | Adequacy of causal laws open |
| Necessary source, sound distinct causes, always some effect | No same particular effect | Witnessed by variable-effects model | Adequacy of world variation open |
| Stable reason plus disjoint reasons for an existent at two worlds | Both at once | Incompatible by `disjoint_reasons_preclude_stable` | Conditional on specified disjointness |
| Same effect plus disjoint effect sets at two accessible worlds | Both at once | Incompatible by `disjoint_effects_preclude_fixed` | Conditional on specified disjointness |

The finite-model certificates check the **exact** canonical Lean declaration
and argument binding for each registered `satisfies` or `violates` evaluation,
including finite carrier exhaustiveness and the absence of axioms. They do
not automatically decide unregistered configurations. The results are not
source-derived readings and do not change any Catholicism-root proof premise.

**Next research step:** (1) compare rigid reasons with world-relative and
counterpart reasons; (2) specify genuine reason sufficiency and whether an
intrinsic essential ground has a necessary modal profile; (3) distinguish
effect identity, causal laws and temporally indexed actions; (4) seek a
stronger general incompatibility core or defended bridge that rules out one
of the presently witnessed formal branches. Every such bridge remains an
**explicit, open premise** until justified.

## Actual-token domains and an overlap bridge (#465, 2026-10-28)

The first slice already proved the alternating countermodel and the
invariance converse; these targets are reused, not counted again. The extension
`TruthCore.Modal.ActualReasonWitness` retains its exact `Model`, `Reason` and
existence facts. In the fixed-roster actualist convention of #599, a supplied
predicate `domain w r` now records actual token membership. This does not
identify tokens with external causal bearers. `Admitted` conjoins membership
with the old explanation relation. `ActualStable` requires one token admitted
at every world **where the selected individual exists**. It makes no claim
about an explanation where that individual is absent. No increasing/decreasing
domain policy is assumed.

A sufficient condition for actual stability is `AnchorOverlap`:
there is a world where the explanandum holds with exactly one admitted reason,
and every other world of its existence shares an admitted reason with that
anchor. Local overlap witnesses initially vary; uniqueness at the anchor
identifies all of them with its unique reason. The Lean theorem
`anchorOverlap_implies_actualStable` implements precisely this inference.
`actualStable_implies_stable` projects to the existing weaker token-only
statement. Neither local PSR nor existence of a necessary bearer supplies
anchor uniqueness or overlap. Indeed overlap already includes local witnesses;
local PSR alone is not an additional hidden premise in this theorem.

Two controls keep the bridge discriminating. `alternating_actual_local` and
`alternating_not_actualStable` reuse the existing two-world alternating model
with exactly its local reason present in each token domain. Even *actual*
local reasons do not validate the shift. `overlapModel` has the same necessarily
existing explanandum in both worlds, one intrinsic-tagged token admitted at
both, and an extra circumstance token only at world `true`. It is sound and
satisfies `overlap_anchor`, but `overlap_not_invariant` shows full invariance
fails: the extra token cannot transfer to world `false`. Thus the sufficient
anchor criterion does not assume invariance of all reasons. Conversely,
`ReasonInvariant` preserves only `explains`, not token-domain membership.
The older invariance theorem concludes token-only `StableExplanation` under
its existence and worldwise-explanation hypotheses; it does not establish
`ActualStable` for independently varying token domains. The certificate
packages the general laws and both controls, with zero allowed axioms.

The exact premise delta is conditional: add an existing anchor, its unique
admitted reason, and anchor-to-world overlap; derive one admitted token on all
worlds of this individual's existence. No new hypothesis is attributed to a
source. If the individual additionally exists in every world, that same token
belongs to every supplied token domain, but no such metaphysical existence is
established here. No actual external bearer, sufficient intrinsic essence,
circularity prohibition, or all-truths PSR is inferred. Existence-PSR remains
restricted to existence facts; contingent-only PSR may leave a necessary
individual unexplained, as the earlier #312 scope controls already show.

The strongest varying-witness rival survives unless overlap is defended;
brute-fact rivals reject the local-PSR starting point. The stable control
exhibits a formal configuration rather than defending necessary-ground
metaphysics. Source attribution is paused by the current owner scope; adequacy
of the tags and the bridge remain open philosophical commitments. Complete
history/external-inventory selection belongs to #467. Intended and actual
Catholicism-root open-premise change: **none**, on every existing route.

## Measure equality across supplied modal interpretations (2026-11-01)

`TruthCore.Modal.NecessaryBeingMeasure` adds an analyst consumer over a supplied
family `m : Ω → Ontic W B`, selected standpoints `w : Ω → W`, and an arbitrary
Mathlib measure `μ` on `Ω`. This is uncertainty between supplied interpretations,
not an automatic representation of logical/proof uncertainty or a respondent's
warrant. It is not a new finite model or an attribution of measure semantics to
the survey's defeasible causal default.

The possible event contains interpretations with an accessible world at which
existing bare `NecessaryBeing` holds. The actual event contains interpretations
with that same predicate at their selected standpoint. `NecessaryBeing` includes
present existence and de-re `NecessaryAt`; it adds no concreteness, causal
capability, explanatory support, God identity or uniqueness. Assuming almost
every interpretation has a Euclidean frame and reflexivity at its selected
standpoint, the two events agree almost everywhere and therefore have equal
measure. The forward direction imports
`NonlimitingConcreteExistence.necessaryAtOrigin`: the SAME individual `c` at
one accessible world supplies actual existence and necessity at the selected
standpoint. The reverse direction selects that standpoint itself by
reflexivity. Only the witness WITHIN each interpretation is retained; there is
no individual shared across `Ω`, nor a shift from `∀ θ, ∃ c` to `∃ c, ∀ θ`.

The measure conclusion uses Mathlib `measure_congr` on almost-everywhere event
equality; any supplied strict threshold is then preserved by equality. The main
statement has one explicit almost-everywhere modal-validity hypothesis, bundling
both frame conditions. It assumes no positive measure or probability threshold
and concludes no interpretation's actuality. Empty interpretation carriers and
zero measures are allowed; they cannot establish existence. No uniform prior,
independence or metaphysical possibility of every interpretation is assumed.

For arbitrary sets, the supplied measure's set-values may be outer-measure
values. The mathematical equality needs no event-measurability or normalization
hypothesis. A probability/credence interpretation additionally requires a
normalized measure, measurable events and coherent semantic-event modeling.
Its almost-sure frame support and any threshold require independent defense;
logical consistency does not provide a uniform prior. This result neither
calibrates a causal default nor derives the selected-case applicability,
reference class, defeater handling, source-Necessary-Being causal capability or
reality of the underlying interpretations. Those commitments remain OPEN.
Existing source claims remain unbound to these new analyst heads. No numerical
God confidence, actual Necessary Being, source soundness or root-premise
closure follows. Final verification is recorded in the focused result/attempt.
