# truth-core

`truth-core` incrementally turns philosophical literature into explicit Lean 4 statements and machine-checked arguments.

The MVP deliberately keeps source evidence, proposition identity, source interpretation, inference, and mechanical verification separate:

1. register stable primary works and immutable passage witnesses;
2. materialize and inspect verified source text before formalization;
3. store statements as independently identified propositions;
4. link source readings to statements through claims without making provenance part of statement identity;
5. represent logical moves as explicit inference applications rather than overloaded graph edges;
6. compose inference applications into arguments;
7. state arguments independently in `Challenge.lean` and prove the same statements in `Solution.lean`;
8. verify the statement/proof boundary with the repository's Rust Comparator.

The public Palomar registry currently targets research mathematics. This repository therefore uses Palomar's mechanical architecture without pretending that its philosophical entries are public Palomar registrations.

## Corpus model

The canonical corpus is **not a DAG**. The global structure may contain mutual implication, contradiction, equivalence relations, or other cycles. A particular proof/explanation may still be projected as an acyclic derivation for visualization.

A statement remains independent even when later work suggests that another statement is textually identical, definitionally equal, logically equivalent, translation-equivalent, philosophically equivalent, or historically intended as the same thesis. Those are additive relations; they do not silently merge IDs.

Source provenance follows a separate `Source → Passage → Claim → Statement` path. A passage identifies reproducible primary-text evidence; a claim identifies an interpretation of that evidence; a statement identifies the proposition used by formal logic.

See [`docs/corpus-model.md`](docs/corpus-model.md) for the entity boundaries and [`docs/source-evidence.md`](docs/source-evidence.md) for the provenance and verification model.

## Why the corpus starts with the Greeks

The seed corpus starts with Plato and Aristotle so later writers can reuse rather than reinvent earlier concepts and source references. In particular, later Aquinas work can point back to Aristotle and Plato through stable classical locators.

Source records preserve conventional citations (Stephanus for Plato, Bekker for Aristotle) and CTS work identifiers where available. Passage records additionally pin the exact digital edition, immutable repository revision, Git blob SHA, and CTS extraction range used by source-derived claims. The Lean declarations contain concise provenance notes, while JSON claims preserve the source-reading relationship separately from statement identity.

## Repository shape

```text
TruthCore/                      Lean source of truth
  Greek/                        source-derived formalizations
  Results/                      verified theorem modules
corpus/
  sources/                      bibliographic/work records
  passages/                     immutable primary-source witnesses and ranges
  statements/                   independent propositions
  claims/                       source interpretations pointing to statements
  inferences/                   explicit logical rule applications
  arguments/                    compositions of inference applications
  relations/                    optional semantic relations; cycles allowed
  candidates/                   small queued source-research tasks
  results/                      mechanical verification metadata
results/<RESULT-ID>/            Comparator configurations
scripts/source_evidence.py      verify/materialize pinned primary-source text
scripts/corpus.py               inspect/validate the work queue and corpus graph
verifier/                       Rust Comparator implementation
scripts/verify-result.sh        run Comparator for one result
scripts/bootstrap-verifier.sh   build pinned verification tools
apps/corpus-explorer/           static scholarly corpus explorer
```

There is intentionally no RDF, graph database, embedding index, identity resolver, or application database in the MVP. Those can be derived later from the verified corpus if a concrete need appears.

## Quick start

Requires Lean via `elan`/`lake`.

```bash
python3 scripts/source_evidence.py check
python3 scripts/corpus.py check
lake build
python3 scripts/corpus.py status
python3 scripts/corpus.py next
python3 scripts/corpus.py frontier --reaching-root
```

`lake build` compiles the source formalizations and proved `Solution` modules. Deliberately incomplete `Challenge` modules are kept out of the normal default build.

### Source evidence

Before formalizing a source-derived claim, materialize its pinned passage instead of relying on model memory:

```bash
python3 scripts/source_evidence.py materialize ARIST-PHYS-I-4
```

The materializer fetches the exact edition at its immutable revision, verifies its Git blob SHA, extracts the configured CTS range where available, and writes normalized UTF-8 text under `.cache/truth-core/sources/`.

To verify all currently pinned source snapshots:

```bash
python3 scripts/source_evidence.py verify
```

`python3 scripts/corpus.py check` also refuses any formalized claim that does not resolve to exactly one registered passage witness. This establishes reproducible **source integrity**. Whether the resulting interpretation is faithful remains a separate scholarly/review question.

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

- **Plato, _Timaeus_ 28a** — a broad causal-principle reading and a stronger distinct-cause reading, intentionally stored as separate source claims and separate statements.
- **Plato, _Timaeus_ 28b–28c** — the cosmos is treated as something that came to be.
- **Two corresponding arguments** — explicit inference applications derive a cause, or a distinct cause, from the relevant causal principle plus the generated-cosmos premise.
- **Aristotle, _Physics_ II.3, 194b–195a** — a first source-derived four-causes classification statement.
- **Aristotle, _Metaphysics_ IV.1, 1003a21ff.** — two readings of inquiry into being qua being.
- **Aristotle, _Categories_ V, 2a11-19** — a primary-substance definition that preserves the two subject-relations introduced in I.2.
- **Aristotle, _Physics_ III.1, 201a10–11** — a weakest relation-preserving definition of change and a separate outcome-indexed reading supported by the immediate examples.

None of these records claims that Lean establishes the historical or philosophical truth of a premise. Source-evidence verification establishes which primary-text witness was consulted; source fidelity remains a distinct research/review question; Lean/Comparator establishes only the formal consequence encoded by a verified argument.

The [Platonic Forms foundation](docs/platonic-forms.md) adds bounded readings from
Phaedo, Parmenides, Republic and Timaeus, with separate classificatory, causal,
exemplar and self-predication commitments and a finite compatibility model.

## Corpus Explorer

The first web application is a static Next.js explorer of the canonical `corpus/` records. It is managed as a Bun workspace with Turborepo so later applications can be added under `apps/` without giving this read-only explorer its own database.

```bash
bun install
bun run dev
```

Run `bun run typecheck`, `bun run test`, `bun run lint`, and `bun run build` to validate the web application. The production build writes the static site to `apps/corpus-explorer/out/`.

The `/skeleton/` view follows the designated root route: checked connections and supporting results, open premises, and explicitly recorded next gaps. A conditional connection is distinct from a discharge from established premises; source support alone discharges nothing.

Claim pages expose the exact pinned primary-source witness and its edition/revision/blob identity separately from the project's interpretation and from any mechanically verified arguments. The explorer preserves the existing claim/result URLs while resolving proposition and argument content through the statement/inference model. A future React Flow composition view should be derived from these records, not stored as canonical graph layout state.

## Worker loop

See [`AGENTS.md`](AGENTS.md). The key invariants are:

> A source worker must materialize and read the pinned primary text before formalizing a claim.
>
> A proof worker must never invent a substantive philosophical premise just to finish a proof. If a premise is missing, it becomes a new source-research candidate.

This makes both source uncertainty and failed proof attempts useful: they expose exactly which evidence or philosophical commitment still needs to be reviewed, sourced, and formalized.
