# Fixed optimal choice and selected effects

This bounded investigation advances the selected-effect bridge, not a new
free-agency theory. Reuse: `SelectedEffectBridge.OutputProfile`, unchanged
`varying` / `NecessaryVariableEffects.alternatingEffects`, and
`Results.Modal.SelectedEffectBridge.selectedEffectNecessary`. The related search
and dossier for `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` were inspected before
new vocabulary; choice-context controls already distinguish fixed conditions
from local functionality. The additional discrimination here concerns the
internal structure of the choice rule: unique optimal option, tied best values,
and absence of an achieved best value.

## Verified source readings

`LEIBNIZ-MONADOLOGY-53-55` was materialized from the existing Latta (1898)
web-snapshot edition (`corpus/passages/leibniz-monadology-en.json`), extending its
selector to anchors 53 through before 56. Read all three sections together:
§53 invokes infinitely many possible universes, only one actual, and sufficient
reason for the choice; §54 locates the reason in fitness/degrees of perfection;
§55 assigns knowledge of the best to wisdom, choice to goodness and production
to power. This is a substantive best-world rationale. These sections do **not**
prove that there is exactly one candidate achieving greatest quality, encode a
numerical metric, or settle the modal status of the rule, alternatives or order.
The definite singular wording does not by itself supply a theorem excluding ties.
No attributed formal claim or uniqueness premise was manufactured from it.

`AQUINAS-ST-I-Q25-A6-EN` was materialized from the complete 1920 Dominican
translation article, including objections and all replies
(`corpus/passages/aquinas-st-i-q25-a6-en.json`). The corpus source `AQUINAS-ST`
already exists. The body distinguishes essential goodness, where making this
thing essentially better changes which thing it is, from goodness beyond essence.
Reply 1 distinguishes the better product from a better manner of divine making;
it denies that God makes from greater wisdom/goodness while permitting better
products. Reply 3 grants optimal ordering with the present creation supposed,
but permits different/additional things yielding another better universe.
Reply 4 limits a blanket improvement reading through the special dignity of
Christ's humanity, beatitude and Mary. The article therefore resists identifying
perfect making with maximizing this creation over unrestricted alternatives.
It does **not** establish `∀ admissible option, ∃ strictly better admissible option`:
that quantifier-strengthening is deliberately rejected. Nor does it establish
that tied optima explain divine choice. These are independently stipulated
logical rivals, not attributed Thomistic teachings.

Both commands succeeded before these readings were written:

```
python3 scripts/source_evidence.py materialize LEIBNIZ-MONADOLOGY-53-55
python3 scripts/source_evidence.py materialize AQUINAS-ST-I-Q25-A6-EN
```

The manifests preserve exact page hashes, selectors and selected-text hashes.
The passages contain the evidence; no long source translations are copied here.
The Theodicy references in Monadology were not independently read, and no
Theodicy claim is made. q19 and Spinoza were not re-audited.

## What the types establish

`Optimal feasible quality x` requires admissibility and Mathlib
`IsGreatest (quality '' feasible) (quality x)`. Quality has a `PartialOrder`, not
a numerical or linear assumption. The set and map are literally fixed across
the modal alternatives; their metaphysical necessity is not established.

`OptimalOutputs` says every output at the selected/accessibly indexed worlds is
optimal, and each performance has some output. This positive-output totality is
separate from at-most-one output. The no-creation alternative to divine creation
is outside this bounded output model. No absent creation is represented by an
existent effect; `none` in the original ontology remains the source.

The general proof takes an actual output `x`, obtains some output `y` at each
accessible performance using totality, proves both optimal, identifies them by
the separate candidate-uniqueness hypothesis, and transports the output fact.
This derives `StableActOutput` rather than assuming its equivalent under a
new name. Existing `selectedEffectNecessary` then adds ubiquitous same-act
performance, causal realization and sound causal endpoints to infer necessity
of that particular actual output. It adds no premise of source necessity and
makes no universal propositional-collapse claim. Actual selected output alone
supplies no all-world output existence.

Any two optimal candidates have equal greatest quality by antisymmetry. The
constant-Nat-quality overlay makes the two original `some false` / `some true`
candidates distinct optima. `varying` and its existence/causal tables are
unchanged; the old soundness, necessary-source, same-act and causal-realization
facts remain reusable. The new certificate explicitly retains local uniqueness,
failed stability and contingency of `firstEffect`. The fixed feasible set
contains both candidates even though one is absent at each selected world;
feasible does not mean simultaneously existent.

Strict improvement of every admissible candidate contradicts an actual optimum,
as the improving candidate cannot lie above a greatest value. `Nat`, all
candidates admissible, and identity quality witness this regime. This does not
prove such a regime metaphysically admissible or attribute it to Aquinas.
Empty feasible sets also satisfy strict improvability vacuously; they likewise
have no optimal candidate. No completeness or exclusivity theorem for these
regimes is claimed: tied best and no-best are controls, not an exhaustive
philosophical dilemma. Perfect agency need not maximize remains an independent
rival outside the selected maximizing hypothesis.

## Verification and premise comparison

The combined full-content source elaborated with no diagnostics through the
coordinator service, workspace `/home/brantner/privat/truth-core-sprint-proof`,
session `causal-harvest`, preview HEAD
`210ab594fb5a1b2af75a6f0af684299937065238`, Scratch path
`Scratch/optimal_creation_choice/Combined.lean`, content SHA256
`a1f5e51cf2861746934e1e8a63250a5eed681621a40fb17d85c889ebed89bbd8`.
This is interactive evidence only. Canonical CI must still build the exact
modules, bind-check and run Comparator/NanoDa. Reproduction of focused proof
checks uses the canonical Solution and its registered result config.

Claim/type self-sweep: no new source claim, inference premise or root route is
introduced. The certificate universally quantifies its conditional backgrounds;
its no-premise argument certifies those conditional consequences and the explicit
controls, not those backgrounds. Its prose preserves fixed feasibility/quality,
positive-output totality, optimal-candidate uniqueness, and all causal hypotheses.
The tied control witnesses the particular finite interpretation only; it is not
a metaphysical possibility or agency proof. Definition/disambiguation records
separate best value, best option and perfect manner of making. Root-premise
comparison intended and actual: none added, removed or discharged. All adoption,
maximizing-rule, uniqueness, positive-output and metaphysical-adequacy questions
remain open.
