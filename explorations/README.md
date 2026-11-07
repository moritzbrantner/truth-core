# Exploration maps

One TOML file per target proposition: the whole argument DAG proposed in one
pass (owner direction 2026-11-07). Reuse existing statement IDs; mark new
candidates with `new = true` and a `text`. Check with
`python3 scripts/argument_batch.py map explorations/<slug>.toml [--mermaid]`.
A map certifies nothing; certify its edges in batches with
`scripts/argument_batch.py records` and record rejected edges as attempts.

```toml
target = "STMT-..."

[[node]]
id = "STMT-EXISTING"

[[node]]
id = "NEW-SOME-STEP"
new = true
text = "Proposed intermediate proposition."

[[edge]]
premises = ["STMT-EXISTING", "NEW-SOME-STEP"]
conclusion = "STMT-..."
kind = "derivation"   # derivation | source | bridge | rival
status = "mapped"     # mapped | certified | rejected
note = "why this step holds or what it needs"
```
