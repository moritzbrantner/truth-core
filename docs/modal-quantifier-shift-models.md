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


## SEP modal intake: designated validity and admissible necessitation (2026-11-06)

Research-only intake against public main `13f1d8f2b3f96687248f7aa1a10e288a29a2a2eb`.
No Lean result, source attribution, proof-calculus adequacy, or premise discharge
is claimed below. The proposed results require a separately frozen implementation.
Policy sourceRevision: `625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

Read the complete current §16, “Quantifiers in Modal Logic”, and complete §10,
“Two Dimensional Semantics”, with §2 and §6 rule/validity context in
[SEP, Modal Logic](https://plato.stanford.edu/entries/logic-modal/)
(substantive revision 2023-01-23). Relevant navigation within §16: paragraphs
beginning “There is another way to formulate quantified modal logics” through
“An alternative treatment would also be need in a temporal logic”, preceded by
the free universal instantiation/generalization discussion. SEP distinguishes
all-world validity from validity at model-designated actuality, describes names
restricted to actual existents, and discusses restrictions on necessitation.
Section 10 supplies the two-index context/evaluation distinction. These are
orientation leads; the exact analyst criterion below is not attributed to SEP,
Deutsch, Kaplan, or Stephanou. Historical attribution remains deferred.

### Exact inventory and rejected duplicates

`related` and `dossier` were run for
`STMT-ACTUALIST-DOMAIN-CORRESPONDENCE`; dossiers for
`STMT-MODAL-EXPLANATION-STABLE` and `STMT-ACTUAL-WORLD-GAP-SCHEMA`
and the existing necessary-individual-quantifier-shift attempt were inspected.

- `TruthCore.Modal.Kripke`: `Frame`, `Formula`, `Holds`, `Valid`.
  `Valid frame formula` means every valuation and every world; `Holds` has no
  actuality/context parameter. `axiomK_valid` is distribution, not a theorem
  allowing local assumptions to be necessitated.
- `TruthCore.Modal.ActualistDomains`: `ActualistAll`, `IncreasingDomains`,
  `DecreasingDomains`, `BoxAllToAllBox`, `AllBoxToBoxAll` use total predicates
  and existence-guarded quantification over one rigid candidate roster.
  `TruthCore.Results.Modal.ActualistDomains.boxAllToAllBox_iff`,
  `allBoxToBoxAll_iff`, `increasing_excludes_contingency`, and `checks`
  already prove the domain correspondences and their joint control. Repeating
  these or saying S5 supplies domain persistence is rejected.
- `TruthCore.Models.PSR.ContingentOnly.model.ontic` has universal access,
  `ExistsAt w x := x = false ∨ (w = false ∧ x = true)`, empty causes.
  `TruthCore.Models.PSR.ContingentOnly.evaluation2` proves
  `ContingentAt ... false true`. Reuse this ontology rather than inventing
  another contingent-name example.
- `TruthCore.Results.Explanation.ActualWorldGap.refl_total`, `rival_not_total`
  and its `schema` already separate the changing diagonal `total w` from the
  fixed content `total a` under a rival. #467 history selection and #751 do not
  establish a rule-admissibility condition for arbitrary designation policies.
  Merely reproving the diagonal/rigid distinction is rejected.
- Repository search found no actuality-extended formula language, free-logic
  proof calculus, designation-closure criterion, or necessitation-admissibility
  theorem. Explanatory “necessitation” results concern reasons entailing effects,
  not the theorem rule. No claim of exhaustive literature novelty is intended.

### Recommended bounded delta: two independent guards on the theorem rule

Fix existing `Frame W` and a predicate `D : W → Prop` of admissible actuality
choices. Keep this same frame, ontology, identity and valuation throughout a
comparison. For a two-index denotation `F : W → W → Prop`, write
`DV_D F := ∀ a, D a → F a a` and
`DN_D F := ∀ a, D a → ∀ v, access a v → F a v`.
Box changes the evaluation coordinate only; it does not change the designated
actuality coordinate. These are semantic validity predicates, not a Lean
provability predicate or truth under a local assumption.

The implementation can freeze the following exact, constructive targets:

1. For context-independent denotations `F a e := P e`,
   `(∀ P : W → Prop, (∀ a, D a → P a) →
      ∀ a, D a → ∀ v, access a v → P v)`
   iff `∀ a, D a → ∀ v, access a v → D v`.
   Reverse direction tests the rule with `P := D`; forward direction applies
   validity at the newly admissible successor. Ordinary `Holds frame val e φ`
   supplies the existing structured modal fragment.
2. For any supplied F, closure of D plus the edge-local transport condition
   `∀ a, D a → ∀ v, access a v → (F v v → F a v)` gives
   `DV_D F → DN_D F`. This condition compares the SAME sentence/content under
   redesignation. It is sufficient, not necessary for an individual F: a
   sentence whose diagonal validity fails makes that instance vacuous.
3. Unrestricted `(∀ F : W → W → Prop, DV_D F → DN_D F)`
   iff `∀ a, D a → ∀ v, access a v → v = a`.
   Necessity uses the transparent diagonal tester `F a e := e = a`;
   sufficiency substitutes equality. This is a denotation-language theorem,
   not an assertion that all such F are expressible in any selected syntax.
   To connect to actual modal content, use the explicit actuality-agreement
   schema `F_P a e := (P e ↔ P a)`: all diagonal instances are true; requiring
   their boxed diagonal validity for every P likewise forces identity access
   at admitted worlds (test `P e := e = a`). This avoids an opaque atom bridge.

Two joint controls are essential. On the unchanged ContingentOnly ontology,
choose `D a := ExistsAt a true` and `P e := ExistsAt e true`. P is true at
EVERY admissible designation, yet the universal frame reaches true where P
fails; content is context-independent, and D is not successor-closed. Next set
`D := True` on the SAME frame and ontology and take
`F a e := (ExistsAt e true ↔ ExistsAt a true)`. Every diagonal is true and D is
closed, yet the boxed instance at false fails at true. Thus admitting all
worlds repairs the first defect without repairing actuality dependence.
The ordinary context-independent fragment with `D := True` is the positive
control and needs no existence persistence. A separate free-logic repair can
retain unrestricted all-world necessitation while denying that a rigid name's
existence is a theorem; a designation-validity approach instead keeps local
name existence and restricts the modal rule. Neither repair is refuted here.

Strongest case: a semantic reason why an admitted-world theorem transports
through box is now explicit, and the two controls distinguish two independent
ways that reason can fail. Strongest objection: a semantic validity criterion
is not a soundness/completeness theorem for Stephanou's syntactic restrictions.
Do not build that calculus in this slice or claim his exact encoding. The
fragment must be described by actual denotations or a checked translation;
“context independent” cannot be asserted from a name's grammatical rigidity.

### Lower-ranked application and remaining bridge

A named-object application can set D to worlds where a fixed rigid referent
exists, or jointly where a supplied finite roster of names exists. Its
successor closure asks persistence of THESE named referents, not automatically
increasing domains for every candidate. This is a useful application of target
1, but alone is too close to the already delivered contingent-name/domain
controls; prefer the combined two-guard package above. A general model-class
redesignation theorem would additionally need a structure-preserving
translation and valuation/name-policy preservation; do not silently generalize
this fixed-structure criterion to arbitrary changing model classes.

Meaning: admissible designation is a semantic policy about which worlds can
serve as an actuality parameter, not evidence that those worlds are real.
An existence-restricted name is a concrete formal example; fictional names do
not satisfy that naming policy. Accessibility means the declared alternatives,
not causation or temporal succession. No seriality, reflexivity, S5, nonempty
D, nonempty domain, or causal law is needed for the generic targets; empty D
makes both sides vacuous. Both explicit controls are populated S5 frames.
The application bridge from natural-language “actual”, names and logical
validity to these two coordinates/policies remains OPEN. Necessary truth,
analytic/context validity, and a justified metaphysical premise stay distinct.

Expected premise comparison: none added, removed or discharged on an existing
root route. The proposed schema adds explicit designation-closure and
content-transport assumptions for the safe rule; the unrestricted alternative
forces the stated degenerate access condition. Existing domain laws, PSR,
causal/explanatory adequacy and root truth are unchanged. The comparison matters
when a worldview argument treats an actuality-valid existential or indexical
principle as a necessary premise: its rule/application bridge must be supplied
rather than obtained from classical validity alone. This intake records a
research result and implementation brief only; no proof has been run.
