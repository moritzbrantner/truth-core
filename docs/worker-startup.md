# Preparing and handing off a worker

Use a standalone clone with the normal truth-core GitHub origin. Preparation requires Python 3, Git, the pinned Lean toolchain via elan, Bun, Cargo and Go. Select the clone explicitly: its root and workspace `node_modules` directories are disposable install output. Worktrees, symlinked clone/install paths, tracked install content and other origins are refused.

```bash
mkdir -p /tmp/moenarch
/usr/bin/time -v flock /tmp/moenarch/truth-core-heavy.lock \
  python3 scripts/prepare-worker.py --clone "$PWD"
```

The helper prints UTC boundaries, exact commands and per-command elapsed seconds. Put Go on `PATH` before invocation (for this machine, the existing installation is `$HOME/.cache/truth-core-go/go/bin`); missing tools fail preflight. It checks Lean against `lean-toolchain`, refuses modified existing dependency checkouts, runs `lake exe cache get` to acquire the manifest-pinned packages and Mathlib's hash-validated prebuilt oleans **before** project compilation, checks each package revision, calls `scripts/bootstrap-verifier.sh`, and installs with:

```bash
bun --config=/dev/null install --linker=hoisted --frozen-lockfile
```

The helper sets `NODE_ENV=development` for installation so an ambient production setting cannot omit development tools. The explicit Bun config prevents an ambient isolated-linker setting from defeating the hoisted install. If an old `.bun` layout exists, the helper validates all install paths before removing the clone's root/workspace install directories. It never deletes `.lake`, resets modified dependencies, changes `HOME`, edits user configuration, or copies a running cache. A quiescent clone can be retained for the next bounded task. `.git/truth-core-preparation.json` stores only Bun/verifier preparation inputs and installed-output fingerprints. Matching inputs and outputs skip those two setup phases; changed or missing outputs fall back to the canonical tools. Bun checks entry metadata and symlink targets; verifier checks binary content, source revisions/edits, toolchain and build inputs. This is readiness metadata, never proof-success evidence. Mathlib cache acquisition retains its own hash validation. Changed pins acquire/rebuild their affected dependencies. A failed acquisition is a failure, not readiness. Stop concurrent writers before preparation; hold the existing heavy-job lock for setup and heavy verification. Memory observations from this trial do not authorize changing that policy.

Readiness means dependencies were prepared. It does not mean a source claim, proof, result or prior check is verified. The helper creates no proof-success marker and does not replace these repository gates:

```bash
scripts/root-imports.sh --write
python3 scripts/docs_index.py --write
scripts/root-imports.sh
python3 scripts/docs_index.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/source_evidence.py check
python3 scripts/source_evidence.py verify
LEAN_NUM_THREADS=2 lake build
python3 scripts/corpus.py check
python3 scripts/corpus.py bind-check
scripts/verify-result.sh <RESULT-ID>
```

Choose affected checks as the worker contract and CI require. Scoped source verification uses `python3 scripts/source_evidence.py verify --base <BASE> --head <HEAD>`; unchanged live witnesses are not refetched by that command. `scripts/affected_results.py select --base <BASE> --head <HEAD>` selects affected results. Keep required NanoDa and Comparator gates; startup cache state never substitutes for them. Merge fresh `origin/main` immediately before pushing, regenerate the shared imports/docs and rerun applicable checks.

Give a fresh proposition worker the four-line brief in `AGENTS.md`, exact statement IDs/theorems, owned paths, required gates and links to repository instructions. When parallel delegation is authorized, prefer a fresh worker with `fork_turns="none"` where supported, a self-contained brief, the research skill path and the relevant issue/current-handoff section. Include the supplied service/setup identity rather than requiring the worker to recover it from parent history. This changes context delivery, not delegation authority. Read mandatory policy once, then refresh instructions whose applicable inputs change. Once the dossier command from #413 is available, inspect `python3 scripts/corpus.py dossier <STMT-ID>` and its recorded attempts before restarting research; preserve new findings there. Do not copy engineering timing into philosophical records.

The repository skill `.agents/skills/truth-core-research/SKILL.md` packages this
research handoff routine. When a coordinator-owned Lean preview is supplied,
use `scripts/agent_lean.py` for full-content diagnostics/goals with automatic
lease and response-binding checks; see [agent-service.md](agent-service.md#client-commands).
The optional native startup hooks provide local context only. They do not
prepare a fresh clone, verify anything or grant merge authority; automatic
execution requires the runtime's exact-definition trust review.

One owner runs each local gate. The master consumes its PR/log evidence and reruns only for an input change, failure, or repository requirement. Keep long jobs in the master, or await their specific process/session handles before the worker exits. A queued shell command is not a completed gate. Hand off pending handles explicitly; do not leave a worker-owned verification process behind. Merge ready PRs serially and coordinate updates with other lanes.

For each of the three trial work items, put this evidence in the existing PR body or check log:

| Field | Record |
| --- | --- |
| Identity | Issue, PR, exact tested head, resolved convention `sourceRevision` |
| Context | Scoped/full inheritance; token usage only if the runtime exposes it |
| Startup | UTC start/end, elapsed seconds, cold/warm state, acquisition/build work observed |
| Research/implementation | Actual interval and whether it is a partial window |
| Local verification | Owner, commands, UTC intervals, results, log path; reason for each repeated gate |
| CI | Workflow/run links and its own start/end interval |
| Review and merge delay | Review request/completion and ready-to-merge/merge times, separately from CI duration |
| Jobs and resources | Pending handles or none; `/usr/bin/time -v` maximum RSS when available |
| Premises | Intended/actual frontier change, or none for engineering |

Use `unavailable`, `pending`, or `partial window` when appropriate. Compare equivalent workloads and cache states; overlapping wall-clock windows do not add to a cycle total. Shared-runner timings and a three-item sample are observations, not a percentage savings estimate or evidence of faster philosophical conclusions. Warm no-op evidence must compare installed artifact content/metadata and source revisions before/after, rather than inferring it from exit code zero. Distinguish tool bookkeeping writes from installs, downloads and compilation. Record whether the trial avoided unchanged-pin cold compilation, lost jobs, duplicate master suites and unexplained gate repetition.
