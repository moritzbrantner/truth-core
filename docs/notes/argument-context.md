# Argument context packs

```bash
python3 scripts/corpus.py context AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE
python3 scripts/corpus.py context <RESULT-ID> --json      # every entry, untruncated
python3 scripts/corpus.py context <STMT-ID>               # only if exactly one argument concludes it
# Optional, after lake build; reads cached .olean files without another build:
python3 scripts/corpus.py context <RESULT-ID> --json --proof-use
python3 scripts/corpus.py lean-reuse --review                  # review missing graph links
python3 scripts/corpus.py lean-reuse --review --json           # every reuse/import classification
```

One call returns a bounded, derived view of one existing argument. It is the
first step when a brief names an existing argument or result as its target or
reuse. Open dossiers only for the premises it reports open.

| Section | Derived from |
| --- | --- |
| Frozen advertised theorem, verbatim, with `file:line` | the result's Challenge module (Lean source) |
| Companion theorems (often omission/independence models) and whether Comparator checks them | the same Challenge module and `comparator.json` `theorem_names` |
| Results reachable through Lean imports, with statement-level graph links | the Solution module's source import closure mapped to result modules (proximity, not proof use) |
| Optional theorem use: theorem-used/graph-linked, theorem-used/not in argument graph, or import only | elaborated Lean proof terms in existing .olean files, plus the corpus argument graph |
| Results whose Solution imports this one | Lean imports |
| Premise and conclusion closure, open depth, and other arguments concluding each one, with their result status and transcription flag | `frontier_report` and argument/result records |
| Downstream arguments, same-bundle duplicates, root routes through the argument | argument records and `frontier_report` routes |
| Registered model evaluations (violations first), `alternative_to`/`attacks`/`refutes` relations, configuration cases | model, relation and configuration records |
| Attempts on these statements or citing the argument/result, newest first, with blockers | attempt records |
| Candidates whose goal or reason names one of these IDs (whole-token match) | candidate records |
| Other open leaves on the root routes through the argument, ranked by number of routes | `frontier_report` routes |
| Corpus IDs cited by the scoped attempts' prose or evidence, ranked by citation count (discovery only) | attempt records |
| Hidden entries of a truncated section, named by ID | the same records |
| Unresolved: open premises, open premises with no other recorded argument, blocked/failed attempts, transcriptions, companion theorems Comparator does not check | everything above |

Nothing here is stored or maintained by hand, and no new proposition format is
added. The corpus JSON records remain authoritative for interpretation, sources
and result status; `frontier_report` remains authoritative for closure. The pack
does no validation (run `corpus.py check`) and no verification
(`scripts/verify-result.sh`), and never upgrades `solution-present`.

By default `context` remains a fast, source-only navigation view: imports are
**not** proof use. After `lake build`, opt into `--proof-use` to inspect existing
olean files with `scripts/LeanReuse.lean`; it **does not run a build**. This walks
the elaborated theorem's proof term, following TruthCore-local helper theorem,
definition and opaque bodies. Each recorded reused result is classified as:

- **theorem-used, graph-linked**: proof-term reference is reachable and its
  recorded conclusion appears among the current argument's premises/commitments;
- **theorem-used, not in argument graph**: reachable theorem without that
  statement-level link, for review (not automatically a defect);
- **import only**: the Solution imports the result module but inspection finds no
  proof-term reference to the advertised theorem.

If the theorem is referenced but its module is absent from the source import
closure, it is still reported with null depth. The inspection is syntactic
reachability, not a minimal logical dependency proof. It follows project-local
bodies and treats library constants as boundaries. It is advisory and must not
create or remove argument edges, amend records, or become a CI failure gate.
`--proof-use-json PATH` on `context` and `--usage-json PATH` on `lean-reuse`
accept saved `LeanReuse.lean` JSON arrays for offline replay. Missing or failed
Lean export entries are errors, not silently relabeled "import only."

## Why: inventory and deficiencies (2026-11-03)

Existing tools are `related` (SQLite/FTS discovery), `dossier` (per statement),
`frontier`/`territory` (root routes), `research_index.py show/bundle/compare`,
`configurations`, `models`, the explorer and the local agent service. They all
start from a **statement**, but research briefs name an **argument or result**
("Reuse: exact Lean theorems"). To rebuild an argument's context an agent ran
`related`, one `dossier` per premise and the conclusion, then opened the Challenge
file and its imports by hand. Concrete deficiencies:

1. **Context size.** `dossier` folds in every definition and argument touching
   a statement. `dossier STMT-GOD-IS-ONE` alone prints 186 KB, because hub
   statements touch root arguments.
2. **Latency.** `dossier` builds every one of the ~2,800 dossiers to print one
   (about 12–20 s per call). A five-statement argument takes over a minute.
3. **No Lean view.** No command shows the frozen theorem text, its companion
   countermodel theorems, or which results a Solution actually imports. Lean
   reuse is invisible in the JSON graph. For example, `ACTUAL-COMMON-ROOT-UNIQUENESS`
   imports 15 results, and none of them is an argument premise.
4. **No argument-level "what is still open".** Other routes to each premise,
   blocked attempts and candidates are spread across separate per-statement
   outputs.

## Measurement

`python3 scripts/context_benchmark.py` replays the merged research PRs in
`scripts/testdata/context-benchmark.json` at their base revisions. The
*needed context* is every existing statement, argument, result, attempt, model,
configuration or candidate ID a PR newly cited, plus every existing result its
Lean files newly import. The anchor is the existing result its new Lean files
import directly. The baseline is `related <conclusion>` plus one `dossier` per
anchor statement. Recall is lexical: an ID counts once it appears in the output.

| PR | anchor | needed | baseline calls/KB/s/recall | context KB/s/recall | context --json KB/recall |
|---|---|---|---|---|---|
| #925 | `COMPLETE-CAUSE-CONNECTED-SOURCE-UNIQUENESS` | 19 | 5 / 200 / 60.8 / 0.53 | 10.0 / 2.3 / 0.53 | 54 / 0.53 |
| #919 | `SOURCE-ROOTED-FROM-CONFLUENCE-AND-SOURCE` | 13 | 5 / 199 / 56.5 / 0.69 | 9.3 / 2.3 / 0.61 | 41 / 0.69 |
| #917 | `AQUINAS-ST-I-Q3-A1-FIRST-BEING-NO-POTENCY` | 27 | 4 / 723 / 45.3 / 0.52 | 15.1 / 2.3 / 0.63 | 193 / 0.81 |
| #916 | `ACTUAL-COVER-NECESSARY-BEING` | 10 | 8 / 935 / 88.7 / 0.70 | 15.8 / 2.1 / 0.80 | 251 / 0.90 |
| #906 | `ACTUAL-COMMON-ROOT` | 10 | 9 / 2654 / 103.4 / 1.00 | 19.5 / 2.1 / 0.90 | 463 / 1.00 |
| #903 | `GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` | 3 | 2 / 17 / 14.9 / 0.33 | 3.0 / 2.4 / 0.33 | 7 / 0.33 |
| **total / mean** | | 82 | 33 / 4729 / 370 / 0.63 | 73 KB / 13.5 / 0.63 | 1008 / 0.71 |

Measured 2026-11-03 at the bases of the listed merges; columns are calls / KB / seconds / recall. The research index was warm for `context`, because the baseline's `related` built it first.

Result: the text pack matches the baseline's recall (0.63) at about 1/65 of its bytes (73 KB against 4.7 MB) and about 25× faster. `--json` reaches 0.71 at about one fifth of the bytes.

The first version, with a fixed 6 entries per section and nothing more, reached only 0.53 (53 KB). #962 added three things:
- a truncated section names its hidden entries by ID;
- the other open leaves on the root routes through the argument, and the corpus IDs cited by its attempts, as ranked ID lines;
- depth-2 Lean consumers.

That raised #917 (a hub of the stage-2 attribute route) from 0.15 to 0.63. The ID lines show at most 40 IDs each (`overflow`). A cap of 25 IDs lowered mean recall to 0.62 (#917 back to 0.52), and the largest pack was still 17.6 KB. So the default stays 40, and packs run to about 20 KB on hub arguments rather than the 15 KB #962 aimed for.

Limits: the sample is six PRs from one author and one week. Recall measures
which IDs were surfaced, not understanding, and the anchor is taken from what
the PR actually imported. The main missed IDs are PR-specific novelties: results
in neighbouring argument families that neither tool links to the anchor.

Deficiencies 1–2 are addressed on the same branch by #958: a single-statement
dossier now takes about 1.4 s, and its default text for `STMT-GOD-IS-ONE` is 15 KB.
The measurement above used the earlier dossier.

Follow-ups (not implemented here): #960 elaborated type and per-hypothesis
binding; #961 agent-service and explorer exposure; #964 lean-lsp-mcp trial.
