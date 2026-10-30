# Proposition discovery index

The primary research entry point is:

```bash
python3 scripts/corpus.py related STMT-Q11-GOD-SUPPOSITUM-IS-NATURE --limit 10
```

The corpus CLI reuses a fresh index or rebuilds missing/stale lookup data
automatically; it performs no Lean preparation or verification. Add `--json` for
complete machine-readable evidence. The lower-level `research_index.py related`
command remains available and rejects stale data rather than refreshing it.

`related` returns propositions with explicit reasons and corpus paths. It ranks
recorded argument connections first (small premise bundles before broad root
arguments), recorded statement-to-statement relations next, shared definitions,
disambiguations and Lean declarations/namespaces next, and weighted paraphrase
word overlap last. Namespace matches indicate proximity, not parsed shared
predicates. Text weights reduce the influence of ubiquitous words; no embeddings
or external service are used.

Argument reasons preserve the complete premise bundle, conclusion, theorem and
recorded result status. A joint premise is never presented as a consequence, and
one member of a bundle is never presented as sufficient for its conclusion.
Known falsity-concluding bundles label their other premises as incompatible
bundle members. This does not select which premise to reject. Directly linked
prior attempts are returned with outcomes and blockers to help avoid repeating
failed investigations. The text output displays up to three reasons per match, with the full reason
count; `--json` retains every reason for each returned match. Increase the
statement limit to inspect more neighbors.

These are discovery rankings, not certified equivalence, strength or entailment.
No cross-profile composition is performed. Source passage coverage remains a
supporting feature, not the primary progress measure.

The JSON corpus remains authoritative. `scripts/research_index.py` builds a
local SQLite/FTS5 index in `.cache/research-index.sqlite` using Python's standard
library. No service, dependency, proof-status registry or Lean preparation is
needed. It does not change philosophical premises or frontier closure.

```bash
python3 scripts/research_index.py build
python3 scripts/research_index.py search 'common nature'
python3 scripts/research_index.py show STMT-GOD-IS-ONE
python3 scripts/research_index.py show results:AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE
python3 scripts/research_index.py duplicates
python3 scripts/research_index.py summary
python3 scripts/research_index.py bundle --case CONFIG-MEGARIAN-CAPACITY-MOTION --premise STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING
python3 scripts/research_index.py compare --case CONFIG-MEGARIAN-CAPACITY-MOTION --left STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING --right STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD
```

Search treats input as literal words joined by AND and returns corpus paths.
`show` returns the full record and reverse references, including relevant
attempts when linked by ID. IDs are namespaced by record kind because an argument
and its result legitimately share an ID. Ambiguous bare IDs require `kind:ID`.
Reverse references are discovery aids: they are not themselves logical edges.

`duplicates` groups exact premise-ID sets with the same conclusion ID. These
are review candidates, not established redundancy: interpretations, commitments
and inference structure can differ. It does not merge statements, identify all
logical equivalents or guarantee that no discovery is repeated.

`bundle` reuses the existing configuration engine in **registered-only** mode.
It exposes applicable registered implications, incompatible subsets and model
references within one existing semantic profile. It refuses propositions outside
that profile. `compare` reuses the existing bounded implication-support search in
both directions, with premise supports and result links. These are candidate
paths, not newly certified compositions. A missing path is unresolved, not
non-entailment, strict strength or compatibility. No cross-profile inference is
performed and no profile is invented for the simplicity–uniqueness cluster.

For actual certification, use the existing gates:

```bash
python3 scripts/corpus.py configurations --case CONFIG-MEGARIAN-CAPACITY-MOTION
python3 scripts/corpus.py configuration-report --help
```

Reuse existing fresh verification evidence where available. This index never
upgrades `solution-present` into verified. Inventory counts are not discovery
counts. The indexed source bytes and index implementation are hashed; every
query rejects stale data. Rebuild after corpus edits. Publication is atomic and
a failed rebuild preserves the old database. The database is disposable and
ignored by Git.

Validation: `python3 -m unittest discover -s scripts -p test_research_index.py`.
Tests cover namespaced identity, inverse references, exact duplicate bundles,
stale input rejection, profile boundaries, uncertified labels and failed rebuild
preservation. No Lean declaration or proof input is modified by this tooling.

## Parity baseline

`python3 scripts/research_index.py parity` independently compares every corpus
JSON file's exact bytes and every top-level ID record's parsed content against
the SQLite projection. Nested passage collections are projected into individual searchable passage
records, preserving each locator alongside its shared snapshot and collection
notes. Other non-entity files, if present, are listed explicitly and preserved
byte-for-byte. This is storage/record parity,
not complete query or corpus-command parity.

`python3 scripts/research_index.py export corpus/statements/god-is-one.json`
prints the original indexed bytes to stdout, preserving formatting and all
fields. Export does not overwrite the corpus. Source files are retained in the
`source_files` table independently of the searchable record projection.

Next parity work should add typed reference resolution, then compare query outputs with the existing corpus commands. Existing
proof, source, dossier and frontier authorities remain unchanged throughout.

## Research workflow integration

`AGENTS.md` places proposition discovery before new investigations and vocabulary.
The existing configuration-elimination loop uses it at the harvest step, followed
by dossiers, exact theorem inspection and established certification. The local
skill `.agents/skills/proposition-reuse/SKILL.md` supplies the same entry point;
it changes no global skill or agent configuration. No Git hook or proof gate is
installed. Discovery is not run on every commit or every diagnostic request.
