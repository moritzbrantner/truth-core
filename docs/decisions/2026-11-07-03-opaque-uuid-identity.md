---
date: 2026-11-07
where: owner decision in session ("we just cannot afford any ambiguity anymore"; "IDs and names need to be clear from now on"); tracked in #1233, section C
---
**Corpus identity is an opaque uuid; names are labels.** Readable ids such as `STMT-NOTHING-PRIOR-TO-ITSELF` encoded words, and therefore senses, into identity, which caused ambiguity and wasted time and tokens.

- Every record id is a uuid. Migrated records get `uuid5(NAMESPACE, "<kind>:<legacy id>")` and keep the old id as `legacy_id`, an alias that never changes; new records get a uuid4. No readable id is minted again.
- Every record has a `label`: required, unique within its kind, at most 100 characters, no uuid-like or id-like text; a term with a linked disambiguated sense carries its sense tag (`PRIOR_1`). `corpus.py check` and `truth check` enforce this with parity.
- Labels made mechanically by the migration that needed a compromise are listed in docs/notes/label-cleanup.md; the list may only shrink (CI ratchet, `scripts/label_cleanup.py`).
- Tools accept a uuid, legacy id or label and print `label [uuid8]`; JSON carries uuids. Record file names, Comparator directories of migrated results, and Lean declaration names are unchanged.

Migration: `scripts/migrate_uuid.py --write` (deterministic and idempotent); losslessness: `scripts/verify_uuid_migration.py --base <pre-migration> --outputs`; branch conversion: docs/notes/uuid-migration.md.
