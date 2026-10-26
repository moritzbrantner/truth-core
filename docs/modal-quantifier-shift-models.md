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
