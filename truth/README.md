# Truth Core CLI

From the repository root with Rust stable (edition 2024) and Python 3:

```sh
cargo build --locked -p truth
target/debug/truth status
target/debug/truth inspect STMT-CATHOLICISM-TRUE --json
target/debug/truth bridges --constants constants.json --target STMT-EXISTING-IN-ACT-AT
target/debug/truth thickness --queue --json
target/debug/truth related STMT-GOD-EXISTS
python3 scripts/corpus.py frontier --json > /tmp/frontier.json
target/debug/truth dossier STMT-GOD-EXISTS --frontier-json /tmp/frontier.json
target/debug/truth context ARGUMENT-ID --frontier-json /tmp/frontier.json --json
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
including cross-record links, semantic constraints, and evidence bindings.
Python also continues to own search, research context, agent service, and
the existing CI and Explorer consumers. Lean and the existing verifier
retain proof authority. Neither Rust command writes a database or cache.

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

## `related`, `dossier`, `context`

These port `scripts/corpus.py related`, `dossier` and `context` (research
navigation, #954 slice 3). The logic lives in library modules with
serde-serializable result structs (`truth::related`, `truth::dossier`,
`truth::context`); `main.rs` only selects output. Text output is
byte-identical to Python's; `--json` prints the Python JSON object plus
`input_identity` (`dossier --all` prints exactly the Python object, keyed by
statement ID). Navigation only: nothing here closes a statement, changes a
route cost or certifies anything.

- `truth related STATEMENT-ID [--limit N]` (default 10; 1 to 200 shown) ranks
  over the loaded corpus in memory. Python ranks over its disposable SQLite
  projection `.cache/research-index.sqlite`; Rust needs and writes no cache.
  The paraphrase-overlap score sums word weights in sorted word order, so
  candidates whose scores differ only in the last floating-point bit may
  order differently from Python (none in the sampled corpus).
- `truth dossier (STATEMENT-ID | --all) --frontier-json FILE [--limit N]`
  (default 8, 0 = all).
- `truth context TARGET --frontier-json FILE [--limit N] [--related N]`
  (defaults 6 and 8; `--related 0` skips the ranking). TARGET is an argument
  ID, a result ID or a statement concluded by exactly one argument. The frozen
  Lean statement and companion theorems are read from each result's Challenge
  module, imports from the Solution modules and permitted axioms from the
  Comparator config, as Python does.

`dossier` and `context` consume the frontier report, which stays the
closure/route authority: `FILE` is `python3 scripts/corpus.py frontier --json
[--root STATEMENT-ID]` written on the same checkout (Rust cannot check that
it is current). Rust reads only the fields these views consume
(`truth::dossier::FrontierView`); once the Rust frontier port lands, it can
build that view in-process and the flag becomes optional. `--frontier-root`
only checks the report's root.

Errors: an unknown ID exits 3 (`unknown_id`); a non-statement `related`
target, an ambiguous `context` target or a missing `--frontier-json` exits 2;
an unreadable or non-frontier report or an unknown report root exits 1.
Python prints the same messages with exit code 2.

Not ported (use Python): `dossier --issues-from` (offline issue snapshot),
`context --proof-use`/`--proof-use-json` (Lean proof-term inspection), the
full `validate()` that `dossier --all` runs first, `research_index.py`'s other
subcommands (`build`, `search`, `show`, `duplicates`, `summary`, `parity`,
`export`, `bundle`, `compare`) and the Explorer's `dossier --all` consumer.
`scripts/verify_truth_cli.py` checks parity on a sample of 30+ statements
(closed, stated, supported, bare, off-frontier and floor-marked), all 3,760
`dossier --all` entries, 15 `context` targets (12 argument IDs, which here
coincide with their result IDs, and 3 uniquely concluded statements) with
several `--limit` values, and the error
cases.

## `bridges`

`bridges` ranks advisory bridge candidates for underived statements by the
Lean constants their declarations share, from a `scripts/StatementConstants.lean`
export (`--constants`) and either `--target ID` or a
`truth thickness --queue --json` or `corpus.py thickness --queue --json` file (`--queue-file`, first `--targets N`,
default 10). It is a search heuristic, not a proof or equivalence judgment;
see `docs/bridge-candidates.md` for the pipeline and the optional Lean trial.
