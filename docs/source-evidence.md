# Source evidence

`truth-core` keeps source integrity, source fidelity, and formal verification separate.

## Three verification boundaries

1. **Source integrity** asks which primary-source bytes were consulted. This is reproducible and mechanically checkable.
2. **Source fidelity** asks whether a claim is a defensible interpretation of those bytes in context. This remains scholarly review and may admit multiple readings.
3. **Formal verification** asks whether a Lean conclusion follows from the advertised formal premises. Lean, NanoDa, and Comparator operate here.

A green result in one layer never implies that the later layers are green. In particular, a hash-verified Aristotle witness does not prove that Aristotle meant a claim, and a Comparator proof does not establish source fidelity.

## Source and passage records

`corpus/sources/` identifies works and their conventional citation systems. `corpus/passages/` identifies reproducible evidence ranges inside immutable digital editions.

Each passage manifest has two parts:

- a **snapshot**, shared by one or more passage ranges, containing the source ID, exact edition URN, language, public repository, immutable revision SHA, file path, Git blob SHA, immutable raw URL, and license;
- one or more **passages**, containing a stable passage ID, conventional human locator, claim-locator prefixes, and an optional CTS extraction path.

The conventional locator remains the citation scholars should read, such as `Physics I.4, 187b7-13` or `Timaeus 28a`. The pinned digital witness answers the different question: exactly which edition bytes did the worker inspect?

## Claim binding

Claims deliberately remain small. A formalized claim records its source ID and precise locator. `scripts/source_evidence.py` requires that pair to resolve to exactly one passage witness.

This keeps proposition identity independent of provenance while making provenance mandatory. Adding a plausible locator to a valid source ID is no longer enough for a claim to pass corpus validation.

## Worker workflow

Before a worker interprets a candidate range:

```bash
python3 scripts/source_evidence.py materialize ARIST-PHYS-I-4
```

The command:

1. resolves the passage manifest;
2. downloads the source file from its immutable revision;
3. recomputes the Git blob SHA and rejects any mismatch;
4. parses the source XML;
5. extracts the configured CTS range when one is available; and
6. writes normalized UTF-8 text under `.cache/truth-core/sources/`.

Workers must read that materialized text and relevant context before creating claims. Model memory, search-result snippets, or an unpinned web page are orientation aids only.

## Validation

Offline structural validation:

```bash
python3 scripts/source_evidence.py check
python3 scripts/corpus.py check
```

Network-backed source verification:

```bash
python3 scripts/source_evidence.py verify
```

CI runs the corpus binding check and verifies the immutable source snapshots. New claims therefore cannot enter the formalized corpus without reproducible source evidence.

## What this does not prove

The source-evidence layer intentionally does not use an LLM score as a truth oracle. It cannot mechanically establish that:

- a paraphrase captures every relevant nuance;
- a chosen formalization has the correct quantifier scope, modality, identity conditions, causal semantics, or historical intent;
- one defensible interpretation is uniquely correct; or
- the philosophical premise itself is true.

Those are handled by explicit interpretation notes, fidelity critique, alternative claims, and human or scholarly review. The source-evidence layer makes that review auditable because the underlying witness is stable and reproducible.
