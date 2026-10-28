# Local agent service

`scripts/agent_service.py` is the bounded experiment from AGENTS.md, "Local
server experiment for the next workloop" (#489). It is a Python-stdlib HTTP
adapter on `127.0.0.1` over commands that already exist:

- corpus operations run `scripts/corpus.py` in the requested workspace, so
  there is no second proof-status registry;
- Lean operations keep one `lake env lean --server` process (LSP) per
  workspace and session id;
- `lake build`, `corpus.py bind-check` and `scripts/verify-result.sh` run as
  queued jobs, one at a time.

Interactive diagnostics do not replace the build, binding, axiom, Comparator
and NanoDa checks on the final inputs.

## Binding

Every response is `{"binding": …, "result": …}` (errors: `{"error": …}` with
a 4xx/5xx status). `binding` names the workspace path, its git `head`, a
`dirty` flag, `diff_sha256` (hash of `git diff HEAD` plus `git status
--porcelain`) when dirty, and `inputs`: the request's arguments and the hashes
of what was read, for example `file_sha256` of a corpus record or
`content_sha256` of the exact Lean text elaborated. A job records
`binding_at_submit` and `binding_at_finish` and sets
`inputs_changed_during_job` when they differ; such a job certifies neither
state.

## Startup and health check

Configure the existing verifier cache once in the repository's **local** git
config (shared by its worktrees), then run one preflight for that toolchain/cache
setup and supply its result to workers:

```bash
git config --local truthcore.verifierHome /absolute/existing/cache
python3 scripts/worker_env.py --check                # optional: --lean-version
```

The wrapper selects `TRUTH_CORE_VERIFIER_HOME` from the explicit environment,
then `truthcore.verifierHome`, then `~/.cache/truth-core-verifier`. It adds
`~/.elan/bin` to `PATH`. The preflight requires the exporter toolchain to match
this checkout's pin and all four existing verifier executables; it prints a
small JSON object naming the checkout, HEAD, toolchain and selected cache.
`--lean-version` additionally probes the installed release with
`elan run <pin> lean --version`, without Elan's `--install` flag, and checks its
version against the pin. It never bootstraps, downloads or changes global
configuration.

After that, wrap commands without repeating the preflight. Arguments, the
caller's working directory and the command's exit status are preserved. The
repository-local config and preflight pin are read from the wrapper's own
checkout even when the command runs elsewhere:

```bash
python3 scripts/worker_env.py -- lake build <focused-target>
python3 scripts/worker_env.py -- scripts/verify-result.sh <RESULT-ID>
```

The master starts and stops the service. Lean requests need the imports of the
edited file built (`lake exe cache get` once for Mathlib, then a `build` job
or `lake build`); `lake env lean --server` does not build imports itself.

```bash
python3 scripts/worker_env.py -- python3 scripts/agent_service.py --port 8765  # optional: --workspace <checkout>
curl -s http://127.0.0.1:8765/health                  # status, toolchain, binding
```

`SIGTERM` or Ctrl-C closes every Lean session (each runs in its own process
group, so no `lean` child is orphaned).

## Workspaces and sessions

Every request may name `workspace` (an absolute path to a truth-core checkout;
default: the service's own checkout) and, for Lean, `session` (default
`default`). Give each worker its own checkout or worktree and session id;
sessions are keyed by both, and each session handles one request at a time.
Lean `path`s are relative to the workspace and must be `.lean` files inside
it.

## Operations

| Request | Wraps |
|---|---|
| `GET /health` | toolchain and binding |
| `GET /corpus/record?id=ID` | the `corpus/*/*.json` record with that `id` (statement, claim, argument, result, definition, …) |
| `GET /corpus/dossier?id=STMT-…` | `corpus.py dossier --json ID` |
| `GET /corpus/frontier[?root=…&reaching_root=1&routes=1]` | `corpus.py frontier --json [--root] [--reaching-root]`, or the text `--routes` report |
| `POST /corpus/check` | `corpus.py check` |
| `POST /lean/diagnostics {path, session?, content?, timeout?}` | open or update the file in the session, wait for elaboration (`textDocument/waitForDiagnostics`), return its diagnostics |
| `POST /lean/goal {…, line, character}` | the same, then `$/lean/plainGoal` and `$/lean/plainTermGoal` at the 0-based position |
| `GET /lean/sessions` | open sessions, their files and versions |
| `POST /lean/close {session}` | shut that session down |
| `POST /jobs {kind: build, targets?}` / `{kind: bind-check}` / `{kind: verify-result, result_id}` | queue the job; returns its `id` |
| `GET /jobs/ID` | status (`queued`, `running`, `passed`, `failed`), queue position, return code, output tail, bindings |

`content` is the full file text to elaborate in memory without writing it to
disk; omit it to elaborate the file on disk. Repeated edits send the new full
text; the session reuses loaded imports, so only the edited file re-elaborates.

## Client commands

These were run against this checkout at the commit that added the service:

```bash
B=http://127.0.0.1:8765
curl -s "$B/corpus/record?id=STMT-CATHOLICISM-TRUE"
curl -s "$B/corpus/dossier?id=STMT-CATHOLICISM-TRUE"
curl -s -X POST "$B/corpus/check"
curl -s -X POST -d '{"kind":"build","targets":["TruthCore.Results.Hiddenness.BeliefWithoutAcceptance.Solution"]}' "$B/jobs"
curl -s "$B/jobs/<id>"
F=TruthCore/Results/Causality/RegressReadingsCoincide/Solution.lean
curl -s -X POST -d "{\"session\":\"w1\",\"path\":\"$F\",\"line\":17,\"character\":2}" "$B/lean/goal"
python3 -c 'import json,sys; print(json.dumps({"session":"w1","path":sys.argv[1],"content":open(sys.argv[1]).read().replace("exact hNoSeries","exact 0")}))' "$F" > /tmp/edit.json
curl -s -X POST --data @/tmp/edit.json "$B/lean/diagnostics"   # returns the type error for the edit
curl -s -X POST -d '{"session":"w1"}' "$B/lean/close"
```

## First measurements

One run on the owner's machine (Mathlib from `lake exe cache get`, imports
built), same file `TruthCore/Results/Causality/RegressReadingsCoincide/Solution.lean`
(imports `Mathlib.Order.WellFounded`):

| Operation | Wall time |
|---|---|
| cold `lake env lean <file>` (CLI check) | 1.9–2.2 s |
| first goal request in a new session (server start, imports, elaboration) | 3.1–3.4 s |
| repeated goal request, warm session | 0.04 s |
| edit sent as `content`, re-elaborate and return diagnostics plus goal | 0.24 s |

The service costs about 1 s more once per session and saves about 2 s on each
later edit or goal query. Corpus calls cost what the CLI costs (`dossier`
about 2 s, `check` about 1 s), since they run it.

## Limits

- No authentication: anything on the machine can call it. Keep it on
  `127.0.0.1`, which is the only address it binds.
- Jobs and sessions live in memory and end with the service.
- Lean sessions in different workspaces may run concurrently; a `build` job in
  a workspace whose sessions are open can change the imports they loaded.
  Reopen (close the session) after a rebuild of imports.
- The retain/revise/remove recommendation belongs in the coordinator's
  handoff, not here.
