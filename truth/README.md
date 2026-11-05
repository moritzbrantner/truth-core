# Truth Core CLI

From the repository root with Rust stable (edition 2024) and Python 3:

```sh
cargo build --locked -p truth
target/debug/truth status
target/debug/truth inspect STMT-CATHOLICISM-TRUE --json
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
