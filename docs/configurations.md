# Executable configurations

`corpus/configurations/*.json` stores research **inputs**, never proof statuses.
Each case names an existing seed statement, one explicit semantics profile,
selected assumption sets, existing incompatible result IDs, optional implication
result IDs and existing finite-model IDs. These records do not enter frontier
closure. Statements, arguments, results, model evaluations and attempts retain
their existing owners.

```bash
# Metadata inspection: explicitly no verified status.
python3 scripts/corpus.py configurations --registered --json
# Live certificates; hold the normal heavy-work lock.
flock /tmp/moenarch/truth-core-heavy.lock \
  python3 scripts/corpus.py configurations --case CONFIG-NECESSARY-INDIVIDUAL --json
# Test a supplied finite assumption set, without enumerating its powerset.
flock /tmp/moenarch/truth-core-heavy.lock \
  python3 scripts/corpus.py configurations --case CONFIG-NECESSARY-INDIVIDUAL \
  --premise STMT-NECESSARY-INDIVIDUAL-DE-DICTO
```

The last command's statement ID must occur in that case's explicit applications;
there is no matching by text or automatic replacement by a similar statement.
`--seed STMT-…` selects cases by their exact seed. Selection IDs and output
ordering are stable. Failure returns nonzero and emits no successful JSON report.

## Persistent contract

A case has these fields:

- `id`: unique `CONFIG-…` identifier; optional `description` explains its purpose.
- `seed_statement_id`: existing dossier statement.
- `semantics`: named `id`, `logic`, `frame`, `domain`, `identity`, `vocabulary`,
  existing Lean `modules`, ordered `parameters`, `applications` and an explicit
  `permitted_axioms` list. Starter profiles permit no axioms. Only the existing
  approved Mathlib axiom names may be allowed by another profile.
- The first slice supports exactly the ordered non-proof semantic roles
  `W : Type`, `I : Type`, `F : TruthCore.Modal.Frame W`,
  `present : I → W → Prop`, and `w : W`. Extra roles, proof-valued parameters,
  changed role types and arbitrary proof-carrying contexts are rejected.
  Parameters use a small names/application/arrows grammar, with no Lean commands
  or tactic bodies. The two carrier types currently have universe zero.
- Optional `constants` fix role names to closed Lean terms (for example
  `{"W": "Nat", "I": "Bool"}`); only literal `Bool`/`Nat` carrier constants are
  supported in this slice, so a fixed proposition cannot turn `w` into a hidden
  proof. `parameter_order` lists every variable and fixed
  role in the original theorem argument order. Fixed roles are explicitly applied
  to each generic theorem, never silently quantified over again.
- `applications` maps existing bound statement IDs to ordered parameter names,
  including implicit type parameters. This is the exact `@Statement args`
  application; argument order is meaningful.
- `configurations`: named `{ "id": "control", "statement_ids": [...] }` sets.
- `incompatibility_result_ids`: existing results whose theorem, at those exact
  shared parameters, derives `False` from its argument's complete premise set.
- `implication_result_ids`: existing non-transcription results whose premise and
  conclusion statements all have explicit applications in this profile.
- `model_bindings`: `{ "model_id": "MODEL-…", "parameters": { ... } }`, mapping
  **every** profile parameter to an existing model registration binding key.
  Every relevant evaluation must use exactly that mapping. Missing evaluations
  remain unknown. Different registrations cannot pool partial satisfaction.
  All registered models in the named vocabulary must be included; a fixed-carrier
  mismatch is explicitly reported as inapplicable and cannot witness the case.

The human-readable settings state the intended interpretation; the executable
profile is its exact shared parameter/application specification. A copied label
alone cannot change what the certificate proves. Profile-specific restrictions
must occur in the encoding or explicit premises; a prose frame label cannot
silently add reflexivity, seriality, nonemptiness or another condition. No
cross-profile certificate transfer or hidden coercion is performed.

## Verification and pruning

The shared result validator checks the exact theorem and Challenge/Solution
modules against the conventional `results/<RESULT-ID>/comparator.json` actually
used by the executable gate. A substituted theorem or alternative config path
cannot borrow another theorem’s successful check.

Default execution rebuilds the profile and result solution modules, compiles a
fresh temporary theorem for every exact shared-parameter implication or
contradiction, and runs each existing Comparator/NanoDa result gate. It then
uses the existing finite-model verifier for the selected registered models.
The original theorem, before profile specialization or currying, independently
passes the existing `BindTypes`/`bind_result` check: every original `Prop`
hypothesis must be one of the argument’s explicit statement premises. Profile
parameters cannot hide a hypothesis or turn a conditional theorem into a fact.
Missing tools, stale proofs, parameter mismatches and failed certificates abort.
The gate also checks `#print axioms` for every specialized theorem, model-role
binding and composed proof against the profile policy. A fixed frame or other
profile constant cannot smuggle `sorryAx` or a stronger logic through an otherwise
zero-axiom generic theorem. False-concluding certificates belong to incompatible
cores and cannot be registered as ordinary implication discoveries.
No success marker or stored report bypasses those gates. `--registered` is an
explicit metadata projection with `verification required` on every selection.
Dossier and static explorer links are registrations, not fresh verification.

A verified incompatible premise set prunes only its supersets within this
profile. Redundant supplied cores are removed by strict inclusion. A remaining
core is advertised as **inclusion-minimal** only when every one-premise removal
has a certified model in the same profile. Those witnesses also cover every
proper subset by monotonicity. Otherwise the report says **minimal among
supplied certificates**, not logically minimal. Failure to find a smaller proof
is never removal evidence.

A model witnesses a configuration only when it certifies every selected
statement at one shared assignment. That establishes formal satisfiability of
this encoding, never metaphysical possibility or general completeness of a
finite model search. Without either certificate the selection stays unresolved.
An overlapping contradictory certificate and model is a verification defect.

Optional implication composition keeps inclusion-minimal sufficient assumption
supports and exact theorem/result provenance. It uses only the supplied verified
rules, not source-support edges, candidate bridges or open transcriptions.
Its explicit work bound reports truncation rather than silently claiming global
minimality. Incompatible selections expose no arbitrary explosive consequences.
This is conditional consequence only; it neither establishes selected assumptions
nor mutates authoritative root-route costs.

## Necessary-individual starter

`CONFIG-NECESSARY-INDIVIDUAL` uses the four exact existing quantifier definitions:
a fixed necessary bearer, necessary exemplification, individual contingency and
joint absence. Two independently certified cores exclude necessary
exemplification with joint absence and a fixed necessary bearer with individual
contingency. Alternating, all-present and all-absent Bool controls cover the
remaining positive subsets; this starter does not manufacture an unknown by
omitting either the second contradiction or a registered witness.

`CONFIG-NECESSARY-INDIVIDUAL-NAT-WORLDS` instead fixes world carrier `Nat` and
individual roster `Bool`. Generic conditional results specialize to those
carriers, but the registered Bool-world controls are explicitly inapplicable.
Necessary exemplification with individual contingency is **unresolved by the
available certified artifacts** in that profile. This is an inventory boundary,
not a claim of logical undecidability, impossibility or metaphysical uncertainty.
No temporal Third Way reading is equated with Kripke accessibility.

First-slice acceptance covers live CLI status, persistent input settings,
certified cores with removal witnesses, registered controls, conservative
unresolved reporting, dossier links and regression fixtures. The static
workspace exposes registered provenance only. It does **not** complete #477's
certified interactive explorer, checked-schema composition and route-impact
acceptance. A later slice must generate a current-head disposable verified
report in the existing proof build and exercise that transport in a browser;
no previous report may become an independent proof-status authority.

Conditional consequence and establishment are separate. The existing corpus may
classify a conditional conclusion as `proved` while its `established` value stays
false because premises remain open. Configuration composition imports neither
label as a premise-free fact: only the explicitly selected assumptions and the
exact verified theorem hypotheses enter its support chains. Report conditional
classification changes separately from changes in established statements or
root-route premises; these configuration inputs discharge none.
