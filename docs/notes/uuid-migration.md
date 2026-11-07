# Uuid migration: converting an in-flight branch

The corpus moved to opaque uuid ids (docs/decisions/2026-11-07-03-opaque-uuid-identity.md,
#1233 section C). `scripts/migrate_uuid.py` is deterministic: a record whose id
is `X` in directory `<kind>s/` becomes `uuid5(NAMESPACE, "<kind>:X")` on every
machine and every branch, keeps `X` as `legacy_id`, and gets a label derived
from its prose. References to known legacy ids become the same uuids. Rerunning
the script on a migrated tree changes nothing.

## Procedure

```bash
git fetch origin
git merge origin/main                      # see "Conflicts" below
python3 scripts/migrate_uuid.py --write    # converts the branch's own new records
python3 scripts/corpus.py check
python3 scripts/label_cleanup.py check --base origin/main
git add -A && git commit -m "Convert branch records to uuid identity"
```

`migrate_uuid.py` converts every record that still has a readable id, rewrites
every reference field to a known legacy id (in the branch's records and in
main's), and derives labels for the converted records. Prose that cites legacy
ids (`STMT-…`, `DEF-…`, `DISAMB-…`) stays as text; it resolves through the
alias table.

### Conflicts

Main rewrote the `id` line (and reference lines) of every record. A record your
branch edited therefore conflicts. The cheapest resolution keeps both sides
mechanical:

1. Before merging, convert the branch itself with main's script:
   `git checkout origin/main -- scripts/corpus_ids.py scripts/migrate_uuid.py scripts/uuid_labels.py`,
   then `python3 scripts/migrate_uuid.py --write` and commit. Both sides now hold
   identical uuid, reference and label lines for records your branch did not
   change, so the merge conflicts only where both sides really changed content.
2. `git merge origin/main`, resolve real conflicts, rerun
   `python3 scripts/migrate_uuid.py --write` (it is a no-op unless something
   still has a readable id), and run `corpus.py check`.

A generated file (`TruthCore/Imports/*`, docs indexes, docs/notes/label-cleanup.*)
in conflict: take either side and rerun its generator; for the label clean-up
files, take main's side and rerun `migrate_uuid.py --write`.

### Labels of your new records

The migration labels your converted records mechanically. The label clean-up
list may only shrink (`scripts/label_cleanup.py check`, CI), so a converted
record whose label the migration had to compromise (truncated, numbered
duplicate, id words, route from the old id, or a term without its sense tag)
fails the ratchet: write a plain, sense-tagged label for it by hand, then run
`python3 scripts/label_cleanup.py prune`, which drops the entries that now pass.

### New work

Never mint a readable id. Give a new record a uuid4 (`python3 scripts/new_id.py`)
and a `label`; `argument_batch.py records` does both for spec records (a spec
names records by handle: a uuid, legacy id or label; a new record needs
`label = "..."` unless its handle is already a plain label). New record files
are `corpus/<kind>/<uuid>.json`; a new result's Comparator config is
`results/<uuid>/comparator.json`.

## Checking losslessness

`python3 scripts/verify_uuid_migration.py --base <pre-migration revision> [--outputs]`
maps every uuid back to its legacy id and checks that each record of the base
revision comes back exactly (so the reference graphs are isomorphic under the
legacy-id bijection), and with `--outputs` that `frontier --json`,
`frontier --routes --json`, `thickness --json` and `thickness --queue --json`
agree after mapping. Ties that used to break by readable id now break by
`legacy_id` (`corpus_ids.order_key`), so no computed choice changed.

## What stayed

- Record file names (`corpus/statements/STMT-….json`, …) and migrated results'
  Comparator directories (`results/<legacy id>/comparator.json`): other tools,
  open branches and history refer to these paths, and renaming would turn every
  in-flight edit into a rename conflict. The result record's
  `comparator_config` names the path; `corpus.py check` accepts the legacy
  directory for a migrated result and requires `results/<uuid>/` otherwise.
- Lean declaration names: they are not corpus ids.
- Exploration maps and batch specs (`explorations/*.toml`, `specs/*.toml`) keep
  their legacy handles; `argument_batch.py` resolves them to uuids.
- Sub-identifiers inside a record (configuration case ids, semantics profile
  ids, case-split cell labels) are not corpus record ids.
