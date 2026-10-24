# Semantic relations

The first records are the premise-program relations of #167 (`alternative_to`, `refutes`; see `docs/corpus-model.md`) and the `supports` relations of #154.

Relations are additive metadata between independently identified corpus entities. They must never silently merge statement identities. The intended JSON shape is:

```json
{
  "id": "REL-...",
  "subject_kind": "statement",
  "subject_id": "STMT-...",
  "predicate": "logically_equivalent_to",
  "object_kind": "statement",
  "object_id": "STMT-...",
  "basis": "ARG-..."
}
```

The global relation graph may contain cycles. Identity, logical equivalence, translation equivalence, philosophical equivalence, contradiction, strength, and other future relations remain distinct predicates.

Premise-program predicates have fixed endpoint kinds, which `corpus.py check` enforces: `alternative_to` (statement → statement), `refutes` (argument → statement; counted only when the argument has a result), `attacks` (statement, claim or argument → statement) and `supports` (claim → statement: source evidence that bears on a premise without stating it; an optional `note` says how far it goes). A `supports` relation is not an inference and closes no premise. `root_route` (argument → statement, and the argument must conclude that statement) designates the argument through which `frontier` enters a statement that several arguments conclude (owner decision on #143, 2026-10-24). `corpus.py frontier` reads them; see `docs/corpus-model.md`.
