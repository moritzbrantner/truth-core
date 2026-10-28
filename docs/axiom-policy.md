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
zero-axiom results. NanoDa's library check (`scripts/verify-library.sh`)
already permitted these three because they reach the library through Lean's
own core; per-result configs now permit them only for Mathlib results.

## What CI checks, and where the trust boundary lies

Three checks run in CI (`.github/workflows/ci.yml`):

1. **Comparator per result** (`scripts/verify-result.sh`). Each result's
   Challenge and Solution are built in a sandbox, exported, compared, and the
   Solution is checked by Lean and by NanoDa. Comparator enforces the result's
   `permitted_axioms`.
2. **Scoped NanoDa over the library** (`scripts/verify-library.sh`, on every
   run whose library changed). `scripts/TruthCoreConstants.lean` lists every
   declaration whose module lies under `TruthCore` (internal names skipped,
   as `lean4export` skips them by default); `lean4export` exports these
   together with the full dependency closure of each, from Mathlib and Lean
   core alike; NanoDa checks the whole export. Nothing a `TruthCore`
   declaration depends on is trusted without being checked. The script
   rejects any exporter diagnostic, because a Lean panic (for example on an
   unparsable name) prints and continues. Every formal/corpus change on `main`, the nightly
   run and any manual run check every `TruthCore` declaration. A pull request
   checks only the declarations of the modules whose build output its diff can
   affect: each changed module and every module that imports one transitively
   (`scripts/affected_results.py nanoda-modules`, passed as
   `verify-library.sh --modules`), each still with its full dependency
   closure. Every other module is unchanged from the PR's base commit, whose
   full check ran on `main`. A change that makes Comparator select every
   result (toolchain, Lake files, verifier, workflows) also runs the full
   check on the PR.
3. **Full NanoDa over everything the library imports**
   (`scripts/verify-library.sh --full`). Beyond check 2, this checks only
   imported declarations that no `TruthCore` declaration uses (about 285,000
   against 19,000 at the Mathlib adoption). These are fixed by
   `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, the NanoDa pin in
   `scripts/verifier-pins.env` and the set of non-`TruthCore` modules the
   library imports (`scripts/affected_results.py external-imports`). CI runs
   it once for each value of that key and caches a marker; a cache hit skips
   it. A PR runs it only when it changes one of those pin files; a new
   external import alone leaves it to the next `main` or nightly run. Its failure would mean NanoDa rejects a pinned Mathlib or Lean core
   declaration that nothing in this repository uses.

So no result relies on the marker: check 2 covers, on every library change
on `main`, every declaration that any `TruthCore` theorem can reach, and on a
PR every declaration whose build output the PR can change. The cached marker
records only that the unused remainder of the pinned dependencies passed once.
A NanoDa failure that a PR's scope missed still turns the next `main` or
nightly run red.

Comparator (check 1) runs on a PR only for the results the diff can affect
(`scripts/affected_results.py select`): those whose own records changed, or
whose Challenge or Solution module, or any `TruthCore` module either imports
transitively, changed. A change to the toolchain, the Lake files, the verifier
scripts or pins, `verifier/`, any tooling script or a workflow selects every
result, as does an unknown input or an unavailable exact diff. Every formal/corpus change on `main`, a nightly
scheduled run and any manual run verify every result, split across parallel
shards (`scripts/verify-all.sh --shard INDEX/COUNT`).

The existing `comparator-plan` computes all heavyweight decisions from the
checked-out PR merge commit against its first parent, or a `main` push against
its previous tip (#568). Nightly and manual runs always request full coverage.
The Actions summary records the reason and each run/bypass decision.

For recognized prose-only changes (`docs/**/*.md` and root `AGENTS.md`,
`CLAUDE.md`, `README.md`, `CONTEXT.md`), `corpus-and-lean` retains import/doc
index checks, corpus validation, offline tests and the frontier report. It
bypasses Lean setup/build, binding and source verification/materialization;
the explorer and Comparator library jobs are skipped. A skip records unaffected
inputs, not a new proof certification. Other Markdown paths are not automatically
prose: an unclassified path takes the full safety path.

Leaf Lean edits retain incremental builds, binding, affected result verification
and scoped NanoDa. Corpus/source JSON edits retain binding, source integrity and
materialization. Both retain explorer unit tests, which read corpus data, index
the real Lean declarations and compare frontier output. Explorer code
edits retain unit tests and both browser variants, with a freshly verified
configuration report from this workflow; report artifacts are never reused from
another head. The stable `comparator` aggregate rejects failed/cancelled work,
missing planner output, and unexpected skips of selected verifiers or the report
producer. Cache keys and the once-per-pin NanoDa marker keep their existing meaning.

## Toolchain pin and rebuilding the verifier

`lean-toolchain` pins the exact Lean version that the Mathlib release in
`lakefile.toml` and `lake-manifest.json` requires (no floating `stable`). To
build:

```bash
lake exe cache get   # download prebuilt Mathlib .olean files
lake build
```

CI runs the same through `.github/actions/lean-setup` (`leanprover/lean-action`
with `use-mathlib-cache: true`). It restores TruthCore's `.lake/build` from the
latest `main` build for the same toolchain and manifest, so Lake's trace hashes
rebuild only stale modules and their dependents. Only `main` runs write that
cache.

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
