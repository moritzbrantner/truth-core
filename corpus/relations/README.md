# Semantic relations

This directory is intentionally empty of JSON records in the seed corpus.

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
