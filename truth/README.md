# Truth Core CLI

From the repository root with Rust stable (edition 2024) and Python 3:

```sh
cargo build --locked -p truth
target/debug/truth status
target/debug/truth check
target/debug/truth inspect STMT-CATHOLICISM-TRUE --json
target/debug/truth bridges --constants constants.json --target STMT-EXISTING-IN-ACT-AT
target/debug/truth thickness --queue --json
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

Rust computes every input itself: the strength order and the set-aside of its
registration arguments, transcription kinds (declared ones and the Lean-text
single-application and assembly heuristics read from each result's Solution
module), the least fixpoint of established and refuted statements that decides
whether a refutation counts (floor bases, defended statements, verified steps,
strength propagation), source depths, the route-aware upward walk and the
reaching-root walk honoring `root_route` relations. No Python runs.
`input_identity` covers the corpus records only, not the Solution modules the
transcription heuristics read.

Not ported: `--base` (it runs the base revision's own `corpus.py` on a
`git archive` extract; use Python), the full `validate()` that the Python
command runs first (Rust performs only the structural load), and the rest of
the frontier report (closure reasons, route costs, items, next steps).
`scripts/corpus.py frontier` and `frontier-diff` remain the closure authority.

## `bridges`

`bridges` ranks advisory bridge candidates for underived statements by the
Lean constants their declarations share, from a `scripts/StatementConstants.lean`
export (`--constants`) and either `--target ID` or a
`truth thickness --queue --json` or `corpus.py thickness --queue --json` file (`--queue-file`, first `--targets N`,
default 10). It is a search heuristic, not a proof or equivalence judgment;
see `docs/bridge-candidates.md` for the pipeline and the optional Lean trial.
