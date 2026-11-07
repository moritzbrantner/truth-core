# Truth Core CLI

From the repository root with Rust stable (edition 2024) and Python 3:

```sh
cargo build --locked -p truth
target/debug/truth status
target/debug/truth check
target/debug/truth inspect STMT-CATHOLICISM-TRUE --json
target/debug/truth bridges --constants constants.json --target STMT-EXISTING-IN-ACT-AT
target/debug/truth thickness --queue --json
target/debug/truth frontier --reaching-root --routes
target/debug/truth --json frontier-diff --base HEAD^1
cargo fmt --all --check
cargo clippy --locked -p truth --all-targets -- -D warnings
cargo test --locked -p truth
python3 scripts/verify_truth_cli.py target/debug/truth
```

After fetching Cargo dependencies, add `--offline` to the build to work without
network access. The executable uses only local files. Use `--root PATH` to
select another checkout. Paths in results are relative to that checkout.

Version 1 JSON uses stdout for results and stderr for errors. Exit codes are
0 for success, 1 for corpus input errors, 2 for usage errors, and 3 for an
unknown exact ID. `inspect` includes every matching kind and its canonical
record fields, including shared argument/result IDs. Passage entries are
expanded with their shared snapshot fields as in the Python reader.
`input_identity` is a non-cryptographic fingerprint of the sorted record
paths and bytes read, including local changes.

`status` counts each record kind and reports structural validation. The
loader checks JSON objects, IDs and per-kind uniqueness, passage manifest
shape, and selected required scalar and list fields. It also counts
configuration records. On malformed input Python and Rust can report
different first errors because they validate different scopes. Python
`scripts/corpus.py status` and `check` still run the full corpus validation,
including cross-record links, semantic constraints, and evidence bindings;
`truth check` (below) ports most of it.
Python also continues to own search, research context, agent service, and
the existing CI and Explorer consumers. Lean and the existing verifier
retain proof authority. Neither Rust command writes a database or cache.

## `check`

`truth check [--json]` ports `python3 scripts/corpus.py check`: `validate()`
and the warnings of `check_warnings()`, rule for rule and in Python's order,
so a broken corpus reports the same first error. On success stdout is
Python's `corpus ok: …` counts line and stderr carries Python's `warning: …`
lines in Python's order; on failure stderr ends with Python's
`corpus error: …` line. Rust exits 1 on a corpus error (Python exits 2;
2 is the CLI's usage code). `--json` prints `counts`, `warnings`, `summary`,
`complete: false` and `python_only`, or a `corpus_error` object.

It is a **partial port**: `scripts/corpus.py check` stays the corpus gate
(CI, `AGENTS.md`). Every run prints a `notice:` line on stderr naming what
still runs only in Python:

- `source_evidence.validate_manifest`: the per-kind passage manifest schema
  (text witness, media span, web snapshot, bibliographic span). Rust loads
  passage manifests and checks their sources, locator-prefix overlaps,
  web-snapshot and bibliographic precedence, and claim binding, basis and
  witness, but not each manifest's fields.
- The opaque-atom transcription warning (`transcription_flags`
  `opaque_atoms`), which needs the Lean definition unfolding not yet ported.

Ported: record loading and ID indexes; finite-model registrations;
configuration cases (`validate_case`, their result configs and the
transcription rejection); attempts; sorted `edition_urns`; source fields;
source-evidence bindings (above); statements (Lean declaration tails, unique
declarations, `self_evident` markings with disagreement and owner approval,
settlement actions); definitions, disambiguations and prose ID citations;
claims (references, status, attribution shape); inferences; arguments
(grounded derivation, term links, sense/disambiguation rule); relations
(entity references, premise-program kinds, `root_route`); candidates; result
Comparator configs (paths, modules, theorem names, axiom policy through the
Mathlib import closure, NanoDa); case splits; schema, `strengthens` and
`strength_comparison` registrations; strength order; `strong_version_needed`;
unused definitions; candidate/result collisions. Warnings: uncounted
refutations, `supports` without a note, constant category predicates (#1103),
strong versions used without `strong_version_needed`, and unmet floor bases,
computed from the same least fixpoint `thickness` uses.

Known message differences: an invalid-JSON error carries serde's parser
message after the shared `cannot read JSON:` prefix; when several entries of
one JSON object are invalid (`strong_version_needed`, profile
`applications`), Rust may name a different first entry, because serde_json
sorts object keys; values Python would crash on (a list where an ID is
expected) are reported, not raised as a traceback.

`scripts/verify_truth_cli.py` compares both on the real corpus (stdout and
every warning line) and on a fixture checkout with a copy of `scripts/*.py`,
so the unmodified Python validator runs on it: the passing fixture (one
warning of each ported kind) and 47 deliberately broken variants, one per
rule, each of which must give the same `corpus error:` line. On the real
corpus (2026-11-07, 3731 statements) the release binary took 0.9–2.6 s and
Python 6.3–16.5 s on the same loaded machine (best of three: 0.9 s vs 6.3 s).

## `thickness`

`truth thickness [--queue] [--frontier-root STATEMENT-ID]` ports
`python3 scripts/corpus.py thickness [--queue] [--root STATEMENT-ID]`
(`--root` already selects the checkout here; the frontier root defaults to
`STMT-CATHOLICISM-TRUE`). Its `--json` output is the Python JSON object plus
`input_identity`; its text output is byte-identical to Python's.
`scripts/verify_truth_cli.py` checks both on the real corpus and on a fixture
corpus. Presentation only: it closes nothing and changes no route cost.

Its inputs (transcription kinds, reaching-root statements, source depths,
upward walks, counted refutations) come from the Rust `frontier` below, so the
two commands share one closure computation. No Python runs. `input_identity`
covers the corpus records only, not the Lean files the transcription
heuristics read.

Not ported: `--base` (it runs the base revision's own `corpus.py` on a
`git archive` extract; use Python) and the full `validate()` that the Python
command runs first (Rust performs only the structural load).

## `frontier` and `frontier-diff`

`truth frontier [--reaching-root] [--routes] [--frontier-root STATEMENT-ID]`
ports `python3 scripts/corpus.py frontier [--reaching-root] [--routes]
[--root STATEMENT-ID]`. Its text output is byte-identical to Python's; its
`--json` output is the Python JSON object plus `input_identity`, including
`next_steps` (the next-work projection with its what-if probes), which, as in
Python, is computed only for `--json` without `--routes`. Rust computes the
whole report itself: the strength order and the set-aside of its registration
arguments; every transcription heuristic (declared kinds, single application,
assembly, opaque Prop atoms, goal as premise consequent after one unfolding of
a `TruthCore/` definition, short proofs); closure rules (a)-(d) with floor
bases, defended statements and strength propagation in one least fixpoint;
closure reasons; per-route open-premise costs; source depths; open items with
their route-aware walks; statement statuses and stages; and the next-step
probes, which rerun the same fixpoint with one leaf established.

`truth frontier-diff --base REV [--head REV] [--frontier-root STATEMENT-ID]`
ports `corpus.py frontier-diff`: the delta between the reaching-root frontier
of the base revision and of the head revision or working tree. Python runs
each revision's own `corpus.py` on a `git archive` extract, so a change of the
frontier rules between revisions shows in the delta. Rust computes a revision
with its own engine only when that revision's `scripts/corpus.py` is
byte-identical (same Git blob) to the checkout's, the rules this port is
verified against; otherwise it runs that revision's Python, exactly as
`corpus.py frontier-diff` does. The working tree is always computed in Rust.
The JSON adds `engines` (`rust` or `python` for base and head) and
`input_identity`; the text output is byte-identical to Python's. It needs
`git` and `tar`, and `python3` for the fallback.

Measured on the real corpus (release build, best of three, one machine,
2026-11-07): `frontier` 10.5 s in Python vs 0.7 s, `frontier --json` (with
next steps) 10.1 s vs 1.3 s, `frontier --reaching-root --routes` 5.3 s vs
0.35 s, `frontier-diff --base HEAD~1` 17.7 s vs 1.8 s (both revisions in Rust).
Python's figures include its full `validate()`.

`scripts/verify_truth_cli.py` checks every form on the real corpus (JSON
equal after dropping `input_identity`/`engines`, text byte-identical; the
diff against `HEAD`) and on a fixture covering every floor basis, an
owner-approved and a stale marking, counted and uncounted refutations,
transcription closure, the warning heuristics, witnesses, a case split and an
unknown root. Not ported: the full `validate()` that Python runs first (Rust
performs only the structural load, so a corpus that Python rejects can still
produce a Rust report). The Python commands, CI's premise-delta step and the
Explorer build still call `corpus.py`; switching them is a later consumer
slice. Lean and Comparator keep proof authority: a "verified" argument is one
with a result record.

## `bridges`

`bridges` ranks advisory bridge candidates for underived statements by the
Lean constants their declarations share, from a `scripts/StatementConstants.lean`
export (`--constants`) and either `--target ID` or a
`truth thickness --queue --json` or `corpus.py thickness --queue --json` file (`--queue-file`, first `--targets N`,
default 10). It is a search heuristic, not a proof or equivalence judgment;
see `docs/bridge-candidates.md` for the pipeline and the optional Lean trial.
