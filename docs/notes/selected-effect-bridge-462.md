# Selected-effect bridge (#462)

This diagnostic completes the bounded act/output discrimination after #481.
It attributes no claim to a historical author. Source interpretation is paused.
The overlay is not a definition of God, free agency, or metaphysical creation.

## Reused evidence and residual question

`TruthCore.Modal.NecessaryVariableEffects.alternatingEffects` already supplies
one necessary source on two universally accessible worlds. Its first effect
exists only at false and its second only at true. `effectsSound`,
`sourceNecessaryAt`, `alwaysCausesSomething`, `noFixedEffect` and
`firstEffectContingent` supply the corresponding exact certificates. The
registered `MODEL-MODAL-FIXED-EFFECT` is the positive comparison with the same
ontology discipline. Those models and the prior quantifier-shift proof are
reused without changing their ontology, registrations or causal relations.

The inventory at main `0f1059ba` also found:

- `BruteFoundationRoutes.necessarySourceAndNecessitatingRule`: a necessary
  source plus an explicit cross-world source-existence-to-effect-existence
  rule entails the selected effect's necessity.
- `BruteFoundationExplanations.necessaryReasonAndNecessitation`: necessary
  reason plus separately stipulated necessitation entails necessary effect.
- `WorldwiseExplanation.worldwise_and_invariance_implies_stable`: worldwise
  reason witnesses require an additional reason-invariance bridge to give one
  stable reason. Stability of an explanation token itself does not make its
  explanandum necessary.

These already answer the bare #312/#319 question about necessary bearer or
reason plus *strict* sufficiency. The remaining bridge was act identity and
output scope. `Results.Isabelle.GoedelGod.ModalCollapse.modalCollapse` concerns necessity
of arbitrary propositions under the Scott axioms, symmetry and excluded middle.
`Results.Isabelle.NotesOnGoedel.ModalCollapse.modalCollapse` instead follows
by explosion from the recorded inconsistent variant; necessity of one effect here
is a strictly narrower conclusion and none of those axiom systems is adopted.

## Act/output control and rejected inference

`OutputProfile` carries one rigid source, a `performs` relation on rigid act
tokens, and a world-relative `output` assignment. The overlay `varying` uses
the **existing** alternating-effects ontology, one Unit act performed in both
worlds, and exactly one output at each world: `some w`. `RealizedOutputs`
connects these assignments to the ontology's causal edges. Causal soundness
separately guarantees that both relata exist and are distinct.

Thus the same token is performed in every world and has at most one output in
each. Moreover, one world-independent function `conditionedOutput c = some c`
describes the output. But its full condition `c = w` varies. Reject the
inference from the identity of this function (or local output uniqueness) to
identity of its arguments or output across worlds. `LocallyDeterministic` is
only at-most-one output per world; it does not assert a complete physical or
metaphysical deterministic theory. No modal freedom conclusion follows from
calling this assignment a countercontrol.

`StableActOutput` adds the missing cross-world restriction: any selected actual
output recurs at each accessible world where that same token is performed.
`fixedConditionsStable` proves that fixed full conditions and the exact fixed
response-function law imply this restriction. `selectedEffectNecessary`
combines the restriction with same-act performance, actual selected output,
causal realization, and sound relata to derive necessity of that effect.
The result neither requires source necessity nor derives same-act performance
from it. Fixed act identity is not itself fixed complete conditions.

| Stage | Retained / added | Selected contingent effect |
| --- | --- | --- |
| Existing alternating ontology | Necessary source, sound distinct relata, some caused effect at every world | Survives |
| Same act | One Unit token performed at every world | Survives |
| Local uniqueness | At most one output per act/world | Survives |
| Fixed response function | `some c` with the full condition `c = w` varying | Survives |
| Stable output | Every actual output recurs wherever the selected act is performed | Excluded given actual output, realization and soundness |
| Fixed full conditions + exact response law | Conditions equal the standpoint condition throughout its accessible worlds | Entails stable output; excludes contingency with the preceding premises |

The last two rows are conditional proof obligations, not established
metaphysical laws. An empty output table would not supply the actual selected
output premise. No reflexivity, symmetry, seriality, or classical axiom is
needed for the general implications. The concrete control is nonempty and
universally accessible. The theorem does not infer an output from the mere
existence of a source, an act, or a capacity.

## Philosophical scope and premise comparison

The primitive world-local causal relation carries no time parameter. It
cannot distinguish first production ex nihilo, ongoing conservation or event
production. It supplies neither a material cause analysis nor a proof that
a historical or theological source intended any of these readings. A table
of co-occurring beings alone is weaker still: the explicit causal realization
law here connects the output assignment to stipulated causal edges, but does
not independently validate those edges as metaphysically sufficient causes.

Free creation and any necessitating full sufficient explanation remain open.
The control is a relative consistency witness for these explicit assignments;
its logical possibility is not evidence of metaphysical possibility.
No root premise is added, removed or discharged. The new closed certificate
packages conditional laws and a checked control; its internal hypotheses are
visible in its definition and do not become established corpus commitments.
The old attempt is updated rather than inventing a source claim to log work.

## Verification and local-service experiment

Challenge SHA256 before solution work:
`9381a9c69c39c365c3f787bd50d8e14c203708d5d87b7a003c996f0a8cd07c1b`.
The Challenge remained unchanged during proof work.

The coordinator-owned service at `http://127.0.0.1:8765` accepted a
self-contained concatenation of the new definition and solution (the latter's
local import omitted), using workspace
`/home/brantner/privat/truth-core-sprint-proof`, persistent session
`causal-harvest`, and unique virtual path
`Scratch/issue462/SelectedEffectBridge.lean`. Requests used an exclusive
`flock` on `/tmp/truth-core-lean.lock`; no checkout or import file was mutated.
Health was checked with `curl -s http://127.0.0.1:8765/health`.
No service, session bootstrap or dependency was started by this worker.

Client: POST `/lean/diagnostics` with JSON fields `workspace`, `session`,
`path`, `content`, `timeout`; POST `/lean/goal` uses the same fields plus
zero-based `line` and `character`. The repeated request additionally appended
`#print axioms TruthCore.Results.Modal.SelectedEffectBridge.checks`.
The response bound workspace revision
`75192b1c3efdf19f25601e52a06116e706420f11`, content SHA256
`312a56c12b04d08bad10c9f3ff3cb4a7db5d332e8fe4cfd03fd971d88057597d`,
and virtual-file version 2. Initial diagnostics reported no errors; the repeat
reported that `checks` depends on no axioms. The goal request at line 87,
character 2 exposed `⊢ p.ontic.ExistsAt v x` with all five bridge hypotheses.

Service-reported times were 0.739 s initially, 0.210 s for the repeat with
axiom inspection, and 0.004 s for the goal lookup; lock waits rounded to
0.000 s. These are interactive feedback timings, not a comparison with a CLI
build or final verification. No CLI latency comparison was run in this lane.
One temporary client edit had an indentation error before making its HTTP
request and was corrected; no service failure or correctness discrepancy was
observed. Retain persistent goal/diagnostic feedback for this bounded use;
leave canonical build, binding, Comparator and NanoDa checks to final CI.
