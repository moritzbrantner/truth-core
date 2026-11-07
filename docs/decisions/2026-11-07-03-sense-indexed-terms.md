---
date: 2026-11-07
where: owner direction in session ("we should use PRIOR_1 and PRIOR_2 in order to disambiguate")
---
**Terms are sense-indexed.** Each argument may use words with several meanings, and the corpus tracks which meaning each argument uses.

- Every disambiguation has a `term_label` and `senses: [{id, label, definition_id}]`. The sense id is an opaque uuid4; the label TERM_n (PRIOR_1) is display-only, stable and only appended.
- One sense per disambiguated term per argument. Mixing senses is an error unless a premise listed in `sense_bridges` relates them.
- An argument that works with several senses becomes one argument per sense, each with fresh uuid ids and a `label` (`for_each_sense` in `argument_batch.py`). A joint fork theorem stays an optional summary.
- Pre-existing mixing arguments are allowlisted (`corpus/sense-index-allowlist.json`) and warned about; see `docs/notes/sense-index-migration.md`.
- Validators that required readable id prefixes also accept uuid4 ids for new records.

See `docs/corpus-model.md`, "Sense-indexed terms", and AGENTS.md, "Encode first".
