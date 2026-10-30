---
name: proposition-reuse
description: Find related truth-core propositions, existing arguments and previous attempts before a philosophical investigation or formalization. Use for corpus research and vocabulary reuse, rather than general repository maintenance.
---

# Proposition reuse

From the truth-core repository root, run:

```bash
python3 scripts/corpus.py related <STMT-ID> --limit 10
python3 scripts/corpus.py dossier <STMT-ID>
```

The first command automatically refreshes its disposable SQLite lookup index.
Use `--json` for complete machine-readable match evidence and attempt blockers.
If no seed ID is known, start with
`python3 scripts/research_index.py build` and
`python3 scripts/research_index.py search 'topic words'`.

Inspect the smallest relevant argument bundles, their exact Lean declarations,
and prior attempts before proposing another result or new vocabulary. Preserve
all displayed premises: a consequence requiring a bundle is not an implication
from any one member. Shared definitions, namespaces and words suggest research
neighbors; they do not establish equivalence or justify merging statement IDs.

Use the existing configuration commands with an explicit semantic profile for
certification. Neither a recorded result status nor a search ranking is fresh
verification evidence. Keep dossier/frontier authorities and existing rules for
persisting substantive attempts; this skill adds no new proof gate or tracker.

See `docs/notes/research-index.md` for index queries and limits, and
`docs/configuration-elimination-loop.md` for the certified investigation loop.
