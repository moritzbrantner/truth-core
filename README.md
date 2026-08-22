# truth-core

`truth-core` incrementally turns philosophical literature into explicit Lean 4 claims and machine-checked arguments.

The MVP deliberately has a small scope:

1. record a stable source and passage locator;
2. formalize one atomic reading of that passage in Lean;
3. keep alternative defensible readings as separate claims rather than forcing a canonical interpretation;
4. state arguments independently in `Challenge.lean`;
5. prove the same statements in `Solution.lean`;
6. verify the statement/proof boundary with the repository's Rust comparator.

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
verifier/                      Rust Comparator implementation
scripts/verify-result.sh       run Comparator for one result
scripts/bootstrap-verifier.sh  build pinned verification tools
apps/corpus-explorer/          static scholarly corpus explorer
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

The Rust Comparator builds the Challenge and Solution independently in Landrun, exports their Lean environments, checks that the advertised theorem and its transitive statement environment match, and rejects non-permitted axioms. Lean checks the freshly built solution; the configs also enable NanoDa as an independent kernel check.

The local bootstrap is intended for reproducible development. Palomar's hosted service has additional registry, policy, sandboxing, disclosure, and editorial machinery that this MVP does not reproduce.

## Seed corpus

The initial vertical slice contains:

- **Plato, _Timaeus_ 28a** — a broad causal-principle reading and a stronger distinct-cause reading, intentionally stored as two claims.
- **Plato, _Timaeus_ 28b–28c** — the cosmos is treated as something that came to be.
- **Two corresponding arguments** — from the relevant causal principle plus the generated-cosmos premise to existence of a cause; each has its own Challenge/Solution pair.
- **Aristotle, _Physics_ II.3, 194b–195a** — a first source-derived four-causes classification claim.
- **Aristotle, _Metaphysics_ IV.1, 1003a21ff.** — two readings of inquiry into being qua being.
- **Aristotle, _Categories_ V, 2a11-19** — a primary-substance definition that preserves the two subject-relations introduced in I.2.
- **Aristotle, _Physics_ III.1, 200b12-15** — queued as the next dependency-oriented candidate on change.

None of these records claims that Lean establishes the historical or philosophical truth of a premise. Lean/Comparator establishes only the formal consequence encoded by the verified argument. Source fidelity remains a distinct research/review question.

## Corpus Explorer

The first web application is a static Next.js explorer of the canonical `corpus/`
records. It is managed as a Bun workspace with Turborepo so later applications can
be added under `apps/` without giving this read-only explorer its own database.

```bash
bun install
bun run dev
```

Run `bun run typecheck`, `bun run test`, `bun run lint`, and `bun run build` to
validate the web application. The production build writes the static site to
`apps/corpus-explorer/out/`.

## Worker loop

See [`AGENTS.md`](AGENTS.md). The key invariant is:

> A proof worker must never invent a substantive philosophical premise just to finish a proof. If a premise is missing, it becomes a new source-research candidate.

This makes failed proof attempts useful: they expose exactly which philosophical commitment still needs to be sourced and formalized.
