# truth-core

`truth-core` incrementally turns philosophical literature into explicit Lean 4 claims and machine-checked arguments.

The MVP deliberately has a small scope:

1. record a stable source and passage locator;
2. formalize one atomic reading of that passage in Lean;
3. keep alternative defensible readings as separate claims rather than forcing a canonical interpretation;
4. state arguments independently in `Challenge.lean`;
5. prove the same statements in `Solution.lean`;
6. verify the statement/proof boundary with [`leanprover/comparator`](https://github.com/leanprover/comparator), the mechanical core used by Palomar.

The public Palomar registry currently targets research mathematics. This repository therefore uses Palomar's mechanical architecture without pretending that its philosophical entries are public Palomar registrations.

## Why the corpus starts with the Greeks

The seed corpus starts with Plato and Aristotle so later writers can reuse rather than reinvent earlier concepts and source references. In particular, later Aquinas work can point back to Aristotle and Plato through stable classical locators.

Source records preserve conventional citations (Stephanus for Plato, Bekker for Aristotle) and CTS work identifiers where available. The Lean declarations themselves contain concise provenance notes, so the formal claim remains reviewable without a separate ontology system.

## Repository shape

```text
TruthCore/                     Lean source of truth
  Greek/                       source-derived claims
  Results/                     verified argument modules
corpus/
  sources/                     bibliographic/source records
  claims/                      one record per interpretation
  candidates/                  small queued formalization tasks
  results/                     result metadata
results/<RESULT-ID>/            Comparator configurations
scripts/corpus.py              inspect/validate the work queue
scripts/verify-result.sh       run real Comparator for one result
scripts/bootstrap-verifier.sh  build pinned verification tools
```

There is intentionally no RDF, graph database, embedding index, or application database in the MVP. Those can be derived later from the verified corpus.

## Quick start

Requires Lean via `elan`/`lake`.

```bash
lake build
python3 scripts/corpus.py check
python3 scripts/corpus.py status
python3 scripts/corpus.py next
```

`lake build` compiles the source claims and the proved `Solution` modules. Deliberately incomplete `Challenge` modules are kept out of the normal default build.

### Comparator verification

The repository pins the verifier revisions used by its bootstrap script. On Linux:

```bash
scripts/bootstrap-verifier.sh
scripts/verify-result.sh PLATO-TIM-28A-28C-COSMOS-CAUSE-A
scripts/verify-result.sh PLATO-TIM-28A-28C-COSMOS-CAUSE-B
```

Comparator builds the Challenge and Solution independently, checks that the advertised theorem has the same statement on both sides, rejects non-permitted axioms, and replays the proof through Lean. The configs also enable NanoDa as an independent kernel check.

The local bootstrap is intended for reproducible development. Palomar's hosted service has additional registry, policy, sandboxing, disclosure, and editorial machinery that this MVP does not reproduce.

## Seed corpus

The initial vertical slice contains:

- **Plato, _Timaeus_ 28a** — a broad causal-principle reading and a stronger distinct-cause reading, intentionally stored as two claims.
- **Plato, _Timaeus_ 28b–28c** — the cosmos is treated as something that came to be.
- **Two corresponding arguments** — from the relevant causal principle plus the generated-cosmos premise to existence of a cause; each has its own Challenge/Solution pair.
- **Aristotle, _Physics_ II.3, 194b–195a** — a first source-derived four-causes classification claim.
- **Aristotle, _Metaphysics_ IV.1, 1003a21ff.** — queued as the next candidate so the Codex loop has real work to continue with.

None of these records claims that Lean establishes the historical or philosophical truth of a premise. Lean/Comparator establishes only the formal consequence encoded by the verified argument. Source fidelity remains a distinct research/review question.

## Worker loop

See [`AGENTS.md`](AGENTS.md). The key invariant is:

> A proof worker must never invent a substantive philosophical premise just to finish a proof. If a premise is missing, it becomes a new source-research candidate.

This makes failed proof attempts useful: they expose exactly which philosophical commitment still needs to be sourced and formalized.
