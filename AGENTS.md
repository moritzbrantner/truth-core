# Codex worker contract

This repository grows one small source claim at a time. Keep the complexity in the philosophy, not in repository machinery.

## Permanent invariants

1. **Research before formalization.** Every source-derived Lean claim must point to a stable source record and a precise locator.
2. **One defensible reading per claim.** If two materially different interpretations are both reasonable, create two claims. Do not hide the difference behind a flag or choose one merely to simplify a proof.
3. **Reuse before invention.** Search existing Lean declarations before adding vocabulary. Reuse only when the meanings genuinely coincide; a false identification is worse than a duplicate concept.
4. **Weakest faithful formalization.** Do not strengthen a source passage to make later arguments easier.
5. **No premise smuggling.** A proof worker may not add an axiom, assumption, definition, or stronger reading solely because a proof needs it. Create a new candidate and source it instead.
6. **Challenge is frozen before solution work.** Never weaken or otherwise edit a Challenge merely to make the Solution pass. If source review changes the statement, treat that as a new/revised claim first.
7. **Formal verification is not source verification.** Comparator proves that the Solution proves the advertised Lean statement with the permitted axioms. It does not establish that the source really meant that statement.
8. **Prefer core Lean.** Add external Lean dependencies only when a philosophical formalization actually needs them.
9. **Do not build future infrastructure early.** No RDF, graph database, embeddings, similarity index, frontend, or generalized ontology layer until the verified corpus creates a concrete need.

## One work item

For `python3 scripts/corpus.py next`, perform this loop:

### 1. Research

- Read the cited passage and enough immediate context to avoid quotation-mining.
- Prefer stable primary-source editions. Preserve the conventional classical locator and a CTS identifier when one exists.
- Record a concise paraphrase rather than copying long translations into the repository.
- Identify one atomic claim or argument.

### 2. Check reuse

Search `TruthCore/` for existing concepts and claims that may express the same thing. Reuse only after checking meaning, not merely similar names.

### 3. Formalize

- Add the smallest Lean declaration that captures the reading.
- Put source locator and interpretation notes in its doc comment.
- Add/update the corresponding `corpus/claims/*.json` record.
- If another reading is also defensible, create a sibling claim with the same source locator and an `interpretation_of` link.

### 4. Critique fidelity

Before proving anything, explicitly ask:

- Is the formal statement stronger than the source?
- Is it weaker in a way that removes philosophically relevant content?
- Did a natural-language relation get replaced by a modern notion with different semantics?
- Did quantifier scope, modality, time, identity, or causation change?

If the answer is materially uncertain, preserve alternatives rather than silently selecting one.

### 5. Create an argument only when there is an argument

A source claim need not have a proof: it may simply be a commitment attributed to a text.

When the corpus contains premises from which a conclusion is meant to follow, add:

- a `Challenge.lean` containing the exact advertised theorem with `sorry`;
- a separate `Solution.lean` containing the same theorem and a real proof;
- a result JSON record;
- a Comparator JSON config naming the theorem and permitted axioms.

### 6. Handle missing premises correctly

If a Solution cannot be proved from the advertised premises:

- do not add an axiom;
- do not strengthen a definition;
- do not broaden an existing source claim;
- create a candidate describing the missing philosophical proposition and the source location that should be investigated.

### 7. Verify

Run:

```bash
lake build
python3 scripts/corpus.py check
scripts/verify-result.sh <RESULT-ID>
```

Do not call a result mechanically verified unless Comparator succeeds. CI also runs an independent no-`sorry` NanoDa check over the built library.

## Naming

Lean namespaces follow the source hierarchy, e.g.:

```text
TruthCore.Greek.Plato.Timaeus
TruthCore.Greek.Aristotle.Physics
```

Claim IDs are stable, uppercase ASCII identifiers whose suffix distinguishes interpretations when necessary:

```text
PLATO-TIM-28A-CAUSE-A
PLATO-TIM-28A-CAUSE-B
```

Result IDs identify an argument, not a source passage:

```text
PLATO-TIM-28A-28C-COSMOS-CAUSE-A
```

Do not renumber existing IDs merely because new earlier material is added.
