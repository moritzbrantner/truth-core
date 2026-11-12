# Label clean-up (uuid migration)

The uuid migration (`scripts/migrate_uuid.py`, docs/notes/uuid-migration.md) derived a
display label for every record from its prose. Labels are mechanical: each was made by
`scripts/uuid_labels.py`, not written by a person. This list names the labels whose
derivation needed a compromise, so they can be fixed in follow-ups. The machine-readable
list is `docs/notes/label-cleanup.json` (`kind`, `id`, `legacy_id`, `label`, `flags`).

`corpus.py check` treats its `untagged-sense` entries as the allowlist for the sense-tag
rule: they are warnings, while a new record with an untagged linked-sense term is an error.
Editing a label is safe: ids never change, and the label only has to stay unique within
its kind, free of id-like text and at most 100 characters. The list may only shrink
(#1233): CI runs `python3 scripts/label_cleanup.py check --base <base>`. After fixing
labels, `python3 scripts/label_cleanup.py prune` removes the entries that now pass.

Flagged labels remaining: 9406.

| flag | count | meaning |
| --- | ---: | --- |
| `truncated` | 9033 | the prose was cut to fit the 100-character limit |
| `duplicate` | 286 | numbered to stay unique within its kind |
| `ids-replaced` | 498 | readable-id tokens in the prose were replaced by their words |
| `from-legacy-id` | 326 | part of the label (an argument's route, or a fallback) came from the old id |
| `fallback` | 0 | no prose to derive a label from |
| `untagged-sense` | 222 | a term with several linked senses (or an undeterminable sense) is untagged |

Flagged labels per kind:

- argument: 969
- attempt: 359
- candidate: 84
- claim: 1927
- configuration: 5
- definition: 1324
- disambiguation: 18
- inference: 1394
- model: 64
- passage: 70
- relation: 533
- result: 75
- source: 9
- statement: 2575
