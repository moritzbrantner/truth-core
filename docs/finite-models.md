# Registered finite interpretations

The library introduced by #414 registers 48 finite interpretations and 334
statement evaluations from existing proofs. A model's `satisfies` or `violates`
value applies to its **closed Lean application**, with its recorded vocabulary,
carrier and assignments. It is not an assertion that a universally parameterized
statement is true or false, that the interpretation is metaphysically possible,
or that any root premise has been established. Registration and successful
attempt records do not participate in frontier closure.

## Looking up an attempted derivation

```bash
python3 scripts/corpus.py models
flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/corpus.py models \
  --check STMT-ACT-SIMPLY-PRIOR-TO-POTENCY \
  --premise STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT
```

Repeat `--premise` to supply the **entire proposed premise set**, or use
`--argument ARG-ID` to take an existing argument's conclusion and complete
premise set. Combining `--argument` with additional `--premise` values strengthens
the tested premise set. A supplied `--check` must match that argument's conclusion.
With no premises supplied, the tested premise set is explicitly empty.

A `counterexample` has a certified failing target and certified satisfaction of
**every requested premise in the same registration**. It rules out the proposed
universal derivation over that vocabulary and those assignments and premises.
It says nothing about derivations with additional premises or different readings.
A `satisfying_interpretation` satisfies the target and all requested premises at
that assignment. This does not establish their metaphysical truth or unqualified
consistency. Missing evaluations stay unknown; neither a missing evaluation nor
a violated premise qualifies the model for either classification. An empty
answer establishes no derivability or consistency result.

`--check` and `--argument` build the registered modules with Lake, then check all
closed applications and their axioms before emitting a report. This catches
stale build output and edits to certificates or registry arguments. Hold the
existing heavy-job lock when running them. `models --verify` performs the same
verification without selecting a target. Plain `models` and dossier/explorer
pages display registrations; they are not independent live verification runs.
Normal `corpus.py bind-check` includes the model gate after checking arguments;
its fixture-only `--lean-json` path does not verify models. `--json` provides the
same projection as text output.

## Record and certificate contract

Each `corpus/models/*.json` file contains one registration:

- `id`: stable `MODEL-…` identity.
- `description`: the original witness and limits of the interpretation.
- `vocabulary`: the explicit comparison group; no group is inferred from prose.
- `lean_declaration`: the named model, frame or tuple of interpretation functions.
- `modules`: existing Lean modules required to elaborate the registration.
- `bindings`: named, closed Lean terms, including carrier types and interpretation
  functions. Only identifiers and numeric tuple projections are accepted;
  arbitrary Lean source is forbidden in JSON.
- `carriers`: binding, nonempty enumerated elements and a theorem certifying that
  every member equals one listed element. Lean checks the element types and
  enumeration; a declared carrier size or a prose claim of finiteness is not evidence.
- `evaluations`: statement ID, `satisfies`/`violates`, ordered binding keys for
  **all** arguments (including type and instance parameters), and a certificate
  theorem declaration. The statement's existing `lean_declaration` determines the
  proposition; JSON cannot substitute a different proposition.

The gate generates a theorem with type `@Statement arguments` for satisfaction
or `¬ (@Statement arguments)` for violation and applies the named certificate.
The Lean compiler must accept it as a closed proof. It also checks the model
term and each enumeration. `#print axioms` must report **no axioms** for every
model term, enumeration and evaluation. `sorryAx`, classical axioms and any
other axiom fail. The generated checking file is temporary; the model definitions,
certificates and registrations are durable repository records. Existing proof
Challenges and statement IDs are preserved. Comparator still checks existing
advertised result obligations, and library verification still runs NanoDa;
the model gate does not replace either boundary.

The eight new component statement records expose already existing PSR, Kant,
Scott and homogeneous-scale definitions at the granularity needed for evaluation.
They are independent propositions with linked definitions and reading distinctions,
not new attributed claims or established philosophical premises.

## Backfill inventory and deliberate boundaries

| Original evidence | Registrations | Preserved witness |
| --- | ---: | --- |
| Q11 nature uniqueness | 3 | Boolean suppositum/nature assignments omitting individuation, identity or common nature |
| Act/potency #374 | 16 | M1–M8, S1–S2 and the six NSense–NRegress omissions |
| Earlier prima-via respect models | 2 | Named strong and weak interpretations |
| Order models #386 | 6 | No causal order, no creatures, tied primary, mutual cause/priority, homogeneous causal control, secondary cause |
| Typed Physics #404 | 14 | Six physical-motion assignments (the first five also occur in the literal-disjunction tests), four self-mover assignments, two scope assignments, two finite first-mover omissions |
| PSR scope #316 | 2 | Original intrinsic-explanation and contingent-only Boolean models |
| Scott/Gödel | 5 | Nonempty one-world Scott model, fixed-positivity A5 omission, invariant-filter model, and the two selected evaluation points of the nontrivial Boolean fragment |

The order registrations use **Mathlib's `Preorder`**, with constructive finite
instances containing only the required fields. Its larger global instances
carry axioms in unused proof fields; those cannot serve the zero-axiom gate.
The secondary-cause model uses `Fin 3`, the finite image of its original Nat
degrees 0,1,2; `sameDegreeOrder` certifies preservation of every degree comparison.
The exhaustive cause table preserves the original assignment without the axiom
dependency of overlapping pattern compilation. These changes add no philosophical
premise and change no existing theorem.

The Physics contact and regress omission witnesses use an infinite successor
chain on `Nat`. The third VIII.5 first-mover omission is infinite too. They are
preserved in their original proofs and deliberately excluded from a **finite**
library. The two-world Boolean counterexamples belong to Scott's 1972 theory;
the 1970 Gödel variant has a separately proved inconsistency, not a satisfiable
finite model. The original empty-world satisfiability loophole is not registered
as a substantive consistency witness; the existing nonempty Scott model is used.
No unavailable prerequisite or omitted finite witness is hidden by these exclusions.

## Co-failure candidates

Pairs are reported only inside one explicit vocabulary group, when both
statements are evaluated in **every** registered model of that group, have the
same failure set, and that set is nonempty. The report names every compared
model and every co-failure model. Missing evaluations exclude a pair rather than
counting as success. With `--check`, only pairs involving the selected target
are shown. These finite observations are **candidate dependencies**, never proved
entailments, source readings or new graph edges. The dossier and explorer expose
each statement's registrations through the same canonical Python projection.
