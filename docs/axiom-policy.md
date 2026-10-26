# Axiom policy for Comparator results

Lean verifies **consequence**, not premise truth. Premises are advertised
statements, so they must never enter a proof as axioms. This page sets which
axioms a Comparator config (`results/<RESULT-ID>/comparator.json`,
`permitted_axioms`) may list. The owner decided it on #337 (2026-10-26),
together with the revision of AGENTS.md invariant 14 that adopts Mathlib.

## The rule

| Result | `permitted_axioms` |
| --- | --- |
| Its Solution does not import Mathlib, directly or through `TruthCore` modules | `[]`: the result stays zero-axiom |
| Its Solution imports Mathlib | `[]`, or exactly `["propext", "Classical.choice", "Quot.sound"]` |

No other axiom is ever permitted: no `sorryAx`, no `Lean.ofReduceBool` or
`Lean.trustCompiler`, and no axiom declared in this repository. A result that
can be proved without the three keeps `[]`, even if it imports Mathlib.

`python3 scripts/corpus.py check` enforces this for every result record
(`permitted_axioms_error` in `scripts/corpus.py`, tested by
`scripts/test_axiom_policy.py`), and `scripts/verify-result.sh` refuses a
config that breaks it before Comparator runs. Comparator then rejects any
axiom the Solution uses beyond the config's list.

## Why these three

`propext` (propositional extensionality), `Quot.sound` (quotient soundness,
which yields function extensionality) and `Classical.choice` are Lean's
standard axioms. Mathlib's real numbers, limits and sums depend on them
throughout, so a proof that uses Mathlib's analysis cannot avoid them.

They are logical and mathematical, not philosophical, axioms. They do
carry one commitment that matters here: `Classical.choice` yields excluded
middle (`Classical.em`). A result that permits the three is a theorem of
classical logic. It must never count as evidence where excluded middle is
itself in question: the frontier around `STMT-EXCLUDED-MIDDLE` and the
intuitionist rival (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`) stay on
zero-axiom results. NanoDa's whole-library check (`scripts/verify-library.sh`)
already permitted these three because they reach the library through Lean's
own core; per-result configs now permit them only for Mathlib results.

## Toolchain pin and rebuilding the verifier

`lean-toolchain` pins the exact Lean version that the Mathlib release in
`lakefile.toml` and `lake-manifest.json` requires (no floating `stable`). To
build:

```bash
lake exe cache get   # download prebuilt Mathlib .olean files
lake build
```

CI runs the same through `leanprover/lean-action` (`use-mathlib-cache: true`).

`lean4export`, which Comparator and NanoDa use to read the built library, is
built for one Lean version. An export built for another version fails with
"incompatible header". After every toolchain bump, rebuild the verifier:

```bash
scripts/bootstrap-verifier.sh   # needs git, lake, cargo and go
```

It checks out the `lean4export` tag that matches the pinned Lean version.
Set `TRUTH_CORE_VERIFIER_HOME` to keep a separate verifier per toolchain.
`verify-result.sh` and `verify-library.sh` stop with a message when the
verifier's `lean4export` was built for a different toolchain.

To bump Mathlib, change `rev` in `lakefile.toml` to a release tag, copy that
tag's `lean-toolchain`, run `lake update`, rebuild the verifier, and run
`scripts/verify-all.sh`.
