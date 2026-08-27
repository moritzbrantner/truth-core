# Corpus model

`truth-core` stores source witnesses, propositions, source readings, inference applications, arguments, and verification results as separate records.

## Core entities

- **Source** — bibliographic identity for a primary work together with its conventional citation system and CTS work identity.
- **Passage** — reproducible source evidence for a coherent range. A passage is tied to an exact digital edition snapshot by immutable revision and Git blob SHA and carries the extraction information needed to materialize the consulted text.
- **Statement** — an independently identified proposition. A statement is not owned by a source passage and is not marked true or verified merely because it exists.
- **Claim** — a scholarly/source claim that a passage supports a statement under a particular interpretation. Existing claim IDs remain stable provenance IDs. A formalized claim must resolve from its source ID and locator to exactly one passage witness.
- **Inference application** — one directed logical step with zero or more scoped assumptions, one or more input statements, an inference rule label, and an output statement.
- **Argument** — a composition of inference applications with advertised premise statements and a conclusion statement.
- **Result** — mechanical verification metadata connecting an argument to its Challenge/Solution theorem and Comparator configuration.
- **Relation** — optional additive metadata such as equivalence, contradiction, translation, strength, or attack. Relations never collapse entity identity.

A passage identifies evidence, not a proposition and not an interpretation. Multiple claims may legitimately use the same passage, and multiple mutually incompatible interpretations may coexist without changing the source witness.

## Provenance path

The intended source-derived path is:

```text
Source → Passage → Claim → Statement → Inference application → Argument → Result
```

The arrows are not all the same kind of relation. `Source → Passage` is bibliographic/evidential containment; `Passage → Claim` is interpretation; `Claim → Statement` associates that interpretation with an independently identified proposition; inference and result records then operate on propositions.

This separation prevents either provenance or proof status from becoming part of statement identity.

## Graph semantics

The canonical corpus is not a DAG. Statements can participate in arguments in either direction, and future semantic relations may be cyclic. A proof or explanation UI may derive an acyclic projection for one chosen derivation, but that projection is a view rather than the ontology.

Inference is never encoded as a bare statement-to-statement edge. For example, modus tollens is represented as two statement inputs (`P → Q` and `¬Q`) consumed by an explicit inference application that outputs `¬P`.

## Identity and equivalence

Statement IDs remain independent even when later evidence suggests two statements are textually identical, definitionally equal, logically equivalent, translation-equivalent, philosophically equivalent, or historically intended as the same thesis. Those are relations that can be added later. They do not mutate or merge existing IDs.

Passage identity is likewise not claim identity. Changing an interpretation does not mutate source evidence. Changing the underlying edition bytes requires a new pinned snapshot rather than silently changing what an existing evidence record points to.

## Verification boundaries

There are three deliberately separate notions of verification:

1. **Source integrity** — `scripts/source_evidence.py` checks that every formalized claim resolves to one passage, that the passage belongs to the registered work, and that the fetched edition bytes match the pinned Git blob SHA. Materialization makes the consulted text reproducible.
2. **Source fidelity** — whether the claim is a defensible interpretation of the materialized passage in context. This remains scholarly/review judgment; materially different defensible readings should be stored separately.
3. **Formal verification** — Lean and Comparator establish that an advertised conclusion follows from advertised formal premises. They do not establish source fidelity or the historical truth of those premises.

No green status is allowed to collapse these boundaries. See `docs/source-evidence.md` for the source workflow.

## Composition and visualization

Large visual compositions should be derived from statements + inference applications + arguments. An argument can be collapsed to a single reusable block whose visible output is its conclusion, then expanded to reveal its internal premises and inference steps. React Flow or another graph renderer should consume such a derived projection; it should not become the canonical data model.

Source views should instead derive their evidence presentation from Source + Passage + Claim records so a reader can inspect the exact witness separately from the project's interpretation and from any later machine-checked argument.
