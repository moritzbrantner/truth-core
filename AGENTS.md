# Codex worker contract

This repository grows one small source reading or argument at a time. Keep the complexity in the philosophy, not in repository machinery.

## Permanent invariants

1. **Research before formalization.** Every source-derived claim must point to a stable source record and a precise locator.
2. **Statements have independent identity.** A statement is a proposition used by logic. A claim says that a source supports a statement under an interpretation. Never make statement identity depend on source provenance.
3. **One defensible reading per claim.** If two materially different interpretations are both reasonable, create two claims. They may point to distinct statements even when later work could relate those statements.
4. **Do not merge by similarity.** Textual identity, translation equivalence, formal equality, logical equivalence, philosophical equivalence, and historical identity are different possible relations. Add relations later; do not silently merge statement IDs.
5. **Reuse before invention.** Search existing statements and Lean declarations before adding vocabulary. Reuse only when the meanings genuinely coincide; a false identification is worse than a duplicate statement.
6. **Weakest faithful formalization.** Do not strengthen a source passage to make later arguments easier.
7. **No premise smuggling.** A proof worker may not add an axiom, assumption, definition, or stronger reading solely because a proof needs it. Create a new candidate and source it instead.
8. **Inference is explicit.** Arguments connect statement IDs through inference-application records. Never encode a logical step as an overloaded bare statement-to-statement edge.
9. **Global cycles are allowed; circular proof is not.** Semantic relations and mutually supporting statements may form cycles. Each advertised argument must still be grounded in its premises and mechanically checked by Lean/Comparator.
10. **Challenge is frozen before solution work.** Never weaken or otherwise edit a Challenge merely to make the Solution pass. If source review changes the statement, treat that as a new/revised claim first.
11. **Formal verification is not source verification.** A result verifies an argument's formal consequence. It does not establish that a source really meant a statement or that a premise is philosophically true.
12. **Prefer core Lean.** Add external Lean dependencies only when a philosophical formalization actually needs them.
13. **Do not build identity infrastructure early.** No graph database, RDF ontology, embedding-based merger, or canonical-equivalence resolver until the corpus creates a concrete need. The typed JSON records are sufficient for now.

See `docs/corpus-model.md` for the entity boundaries.

## One work item

For `python3 scripts/corpus.py next`, perform this loop:

### 1. Research

- Read the cited passage and enough immediate context to avoid quotation-mining.
- Prefer stable primary-source editions. Preserve the conventional classical locator and a CTS identifier when one exists.
- Record a concise paraphrase rather than copying long translations into the repository.
- Identify one atomic source reading or argument.

### 2. Check reuse

Search `corpus/statements/` and `TruthCore/` for existing propositions and concepts that may express the same thing. Reuse a statement ID only after checking meaning, not merely similar names. When uncertain, preserve separate statement identities; equivalence can be related later.

### 3. Formalize a source reading

- Add the smallest Lean declaration that captures the proposition when a Lean declaration is appropriate.
- Put source locator and interpretation notes in the Lean doc comment.
- Add/update an independent `corpus/statements/*.json` record for the proposition.
- Add/update the corresponding `corpus/claims/*.json` record linking the source reading to that statement.
- If another reading is also defensible, create a sibling claim with the same source locator and an `interpretation_of` link. Do not use that link to imply statement equivalence.

### 4. Critique fidelity

Before proving anything, explicitly ask:

- Is the formal statement stronger than the source?
- Is it weaker in a way that removes philosophically relevant content?
- Did a natural-language relation get replaced by a modern notion with different semantics?
- Did quantifier scope, modality, time, identity, or causation change?

If the answer is materially uncertain, preserve alternatives rather than silently selecting one.

### 5. Create an argument only when there is an argument

A source claim need not have a proof: it may simply be a commitment attributed to a text.

When statements are meant to support a conclusion:

- ensure every premise and conclusion has its own statement record;
- add one or more `corpus/inferences/*.json` records for the logical steps;
- add a `corpus/arguments/*.json` record composing those steps;
- add `Challenge.lean` containing the exact advertised theorem with `sorry`;
- add a separate `Solution.lean` containing the same theorem and a real proof;
- add a `corpus/results/*.json` verification record that points to the argument;
- add a Comparator JSON config naming the theorem and permitted axioms.

Scoped assumptions and discharged assumptions belong to inference records. They are not ordinary established corpus premises.

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

Do not call an argument mechanically verified unless its result passes Comparator. CI also runs an independent no-`sorry` NanoDa check over the built library.

## Naming

Lean namespaces follow the source hierarchy, e.g.:

```text
TruthCore.Greek.Plato.Timaeus
TruthCore.Greek.Aristotle.Physics
```

Claim IDs are stable provenance/interpretation IDs:

```text
PLATO-TIM-28A-CAUSE-A
PLATO-TIM-28A-CAUSE-B
```

Statement IDs are stable proposition IDs and should not encode an assertion that two source readings are identical:

```text
STMT-CAUSE-PRINCIPLE-BROAD
STMT-COSMOS-HAS-CAUSE
```

Argument IDs identify a composed derivation. Result IDs identify a verifier record and may intentionally match the argument ID in the seed corpus:

```text
PLATO-TIM-28A-28C-COSMOS-CAUSE-A
```

Do not renumber existing IDs merely because new earlier material is added.
