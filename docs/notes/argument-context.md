# Argument context packs

```bash
python3 scripts/corpus.py context AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE
python3 scripts/corpus.py context <RESULT-ID> --json      # every entry, untruncated
python3 scripts/corpus.py context <STMT-ID>               # only if exactly one argument concludes it
```

One call returns a bounded, derived view of one existing argument. It is the
first step when a brief names an existing argument or result as its target or
reuse. Open dossiers only for the premises it reports open.

| Section | Derived from |
| --- | --- |
| Frozen advertised theorem, verbatim, with `file:line` | the result's Challenge module (Lean source) |
| Companion theorems (often omission/independence models) and whether Comparator checks them | the same Challenge module and `comparator.json` `theorem_names` |
| Results reused through Lean, transitively, each marked `graph-linked` or `import only` | the Solution module's `import` closure mapped to result modules |
| Results whose Solution imports this one | Lean imports |
| Premise and conclusion closure, open depth, and other arguments concluding each one, with their result status and transcription flag | `frontier_report` and argument/result records |
| Downstream arguments, same-bundle duplicates, root routes through the argument | argument records and `frontier_report` routes |
| Registered model evaluations (violations first), `alternative_to`/`attacks`/`refutes` relations, configuration cases | model, relation and configuration records |
| Attempts on these statements or citing the argument/result, newest first, with blockers | attempt records |
| Candidates whose goal or reason names one of these IDs (whole-token match) | candidate records |
| Unresolved: open premises, open premises with no other recorded argument, blocked/failed attempts, transcriptions, companion theorems Comparator does not check | everything above |

Nothing here is stored or maintained by hand, and no new proposition format is
added. Lean stays authoritative for the theorem's type and for actual reuse. The
JSON records stay authoritative for interpretation, sources and status;
`frontier_report` stays authoritative for closure. The pack does no validation
(run `corpus.py check`) and no verification (`scripts/verify-result.sh`), and it
never upgrades `solution-present`. The theorem text is the source text of the
frozen Challenge. The type elaborated after `lake build` is what `bind-check`
compares. An `import only` reuse can be a vocabulary import, or a dependency the
argument graph does not record. It is a review hint, not a missing edge.

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
| #925 | `COMPLETE-CAUSE-CONNECTED-SOURCE-UNIQUENESS` | 19 | 5 / 200 / 53.2 / 0.53 | 9.1 / 2.3 / 0.53 | 53 / 0.53 |
| #919 | `SOURCE-ROOTED-FROM-CONFLUENCE-AND-SOURCE` | 13 | 5 / 199 / 50.7 / 0.69 | 8.2 / 2.3 / 0.46 | 40 / 0.54 |
| #917 | `AQUINAS-ST-I-Q3-A1-FIRST-BEING-NO-POTENCY` | 27 | 4 / 723 / 38.9 / 0.52 | 8.7 / 2.1 / 0.15 | 185 / 0.78 |
| #916 | `ACTUAL-COVER-NECESSARY-BEING` | 10 | 8 / 935 / 97.5 / 0.70 | 10.4 / 2.2 / 0.80 | 245 / 0.90 |
| #906 | `ACTUAL-COMMON-ROOT` | 10 | 9 / 2654 / 96.6 / 1.00 | 13.3 / 2.6 / 0.90 | 453 / 1.00 |
| #903 | `GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` | 3 | 2 / 17 / 14.7 / 0.33 | 2.9 / 2.1 / 0.33 | 7 / 0.33 |
| **total / mean** | | 82 | 33 / 4729 / 352 / 0.63 | 53 KB / 13.6 / 0.53 | 982 / 0.68 |

Measured 2026-11-03 at the bases of the listed merges; columns are calls / KB / seconds / recall. The research index was warm for `context`, because the baseline's `related` built it first.
Result: the text pack is about 90× smaller and 26× faster, with somewhat lower recall (0.53 against 0.63). Most of the gap is text truncation: `--json` reaches 0.68 at about one fifth of the baseline's bytes. #917 shows the trade-off most clearly: the anchor is a hub of the stage-2 attribute route, and the text caps hide 17 needed IDs that `--json` returns (text misses 23, `--json` 6).

Limits: the sample is six PRs from one author and one week. Recall measures
which IDs were surfaced, not understanding, and the anchor is taken from what
the PR actually imported. The main missed IDs are PR-specific novelties: results
in neighbouring argument families that neither tool links to the anchor.

Deficiencies 1–2 are addressed on the same branch by #958: a single-statement
dossier now takes about 1.4 s, and its default text for `STMT-GOD-IS-ONE` is 15 KB.
The measurement above used the earlier dossier.

Follow-ups (not implemented here): #959 theorem use versus vocabulary imports; #960 elaborated
type and per-hypothesis binding; #961 agent-service and explorer exposure;
#962 hub-aware ranking for text recall.
