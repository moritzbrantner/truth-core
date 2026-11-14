# Preparing and handing off a worker

Use a standalone clone with the normal truth-core GitHub origin. Preparation requires Python 3, Git, the pinned Lean toolchain via elan, Bun, Cargo and Go. Select the clone explicitly: its root and workspace `node_modules` directories are disposable install output. Worktrees, symlinked clone/install paths, tracked install content and other origins are refused.

```bash
mkdir -p /tmp/moenarch
/usr/bin/time -v flock /tmp/moenarch/truth-core-heavy.lock \
  python3 scripts/prepare-worker.py --clone "$PWD"
```

**Reuse a warm clone.** Retain a quiescent prepared clone for the next bounded task when possible. For a new clone, seed TruthCore's own build output from a warm clone with the same `lean-toolchain`, `lake-manifest.json` and `lakefile.toml` (a nearby revision is fine):

```bash
/usr/bin/time -v flock /tmp/moenarch/truth-core-heavy.lock \
  python3 scripts/prepare-worker.py --clone "$PWD" --seed-build-from <WARM-CLONE>
```

The warm clone must be a standalone truth-core clone that this machine's workers own and that no one writes to during the copy; holding the heavy-job lock ensures that when every builder takes it. Seeding copies only an absent `.lake/build` (with `cp -a --reflink=auto`, never hardlinks, so a rebuild in one clone cannot rewrite the other's outputs) into a staging directory, compares entry metadata of the source before and after and of the copy, and discards the copy on any difference. It refuses different build inputs, symlinks and leftover staging; an existing `.lake/build` is kept for Lake to reconcile. Mathlib still comes from `lake exe cache get`. Lake keys each module's trace on its source, imports, options and toolchain, so the next `lake build` replays unchanged modules and rebuilds every changed module and its dependents. Lake does not rehash replayed outputs, so a seed is as trustworthy as the clone it came from; the gates below still run on the final inputs.

Observed on this machine (2026-11-05, `LEAN_NUM_THREADS=2`, Lean 4.35.0, about 2,000 modules): cold `lake build` about 13.5 minutes; copying a 485 MB build output 4 seconds; first build of a seed from a warm clone 51 commits behind 29–44 seconds (14 modules rebuilt); then one changed leaf module 15 seconds (it and its two aggregators). These are observations, not a guarantee.

The helper prints UTC boundaries, exact commands and per-command elapsed seconds. Put Go on `PATH` before invocation (for this machine, the existing installation is `$HOME/.cache/truth-core-go/go/bin`); missing tools fail preflight. It checks Lean against `lean-toolchain`, refuses modified existing dependency checkouts, runs `lake exe cache get` to acquire the manifest-pinned packages and Mathlib's hash-validated prebuilt oleans **before** project compilation, checks each package revision, calls `scripts/bootstrap-verifier.sh`, and installs with:

```bash
bun --config=/dev/null install --linker=hoisted --frozen-lockfile
```

The helper sets `NODE_ENV=development` for installation so an ambient production setting cannot omit development tools. The explicit Bun config prevents an ambient isolated-linker setting from defeating the hoisted install. If an old `.bun` layout exists, the helper validates all install paths before removing the clone's root/workspace install directories. It never deletes `.lake`, resets modified dependencies, changes `HOME`, edits user configuration, or keeps a copy of a build output that changed while it was copied. A quiescent clone can be retained for the next bounded task. `.git/truth-core-preparation.json` stores only Bun/verifier preparation inputs and installed-output fingerprints. Matching inputs and outputs skip those two setup phases; changed or missing outputs fall back to the canonical tools. Bun checks entry metadata and symlink targets; verifier checks binary content, source revisions/edits, toolchain and build inputs. This is readiness metadata, never proof-success evidence. Mathlib cache acquisition retains its own hash validation. Changed pins acquire/rebuild their affected dependencies. A failed acquisition is a failure, not readiness. Stop concurrent writers before preparation; hold the existing heavy-job lock for setup and heavy verification. Memory observations from this trial do not authorize changing that policy.

Readiness means dependencies were prepared. It does not mean a source claim, proof, result or prior check is verified. The helper creates no proof-success marker and does not replace these repository gates:

```bash
scripts/root-imports.sh --write
python3 scripts/docs_index.py --write
scripts/root-imports.sh
python3 scripts/docs_index.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/source_evidence.py check
LEAN_NUM_THREADS=2 lake build
cargo build --locked --release -p truth
target/release/truth check
python3 scripts/bundle_audit.py
python3 scripts/corpus.py bind-check
scripts/verify-result.sh <RESULT-ID>
```

Choose affected checks as the worker contract and CI require. Source and attribution gates run offline; materialize individual passages only when doing selected source research. `scripts/affected_results.py select --base <BASE> --head <HEAD>` selects affected results; `python3 scripts/corpus.py bind-check --affected --base <BASE>` binds just those (against the working tree unless `--head` is given), and `bind-check --result <ID>` (repeatable) binds named results. Both need only the selected Solution modules built; the stale-pin and registered-model checks run only in the full `bind-check`, which CI runs. Keep required NanoDa and Comparator gates; startup cache state never substitutes for them. Merge fresh `origin/main` immediately before pushing, regenerate the shared imports/docs and rerun applicable checks.

Give a fresh proposition worker the [research brief](../AGENTS.md#worker-brief-and-handoff)
and [scoped execution context](systematic-corpus-loop.md#worker-ownership-and-integration),
including its policy revision, checkout, ownership/authority, service setup and
existing check evidence. Retain that worker through repairs to the same slice.
Read mandatory policy once, then refresh changed applicable inputs. Inspect
`target/release/truth dossier <STMT-ID>` and its recorded attempts before restarting
research; preserve new findings there. Keep engineering timing out of philosophical
records. Designate warm clones explicitly and exclude them from disposable-clone
cleanup under the ownership contract, preserving `target/release/truth` and Lean
build seeds for reuse.

The repository skill `.agents/skills/truth-core-research/SKILL.md` packages this
research handoff routine. When a coordinator-owned Lean preview is supplied,
use `scripts/agent_lean.py` for full-content diagnostics/goals with automatic
lease and response-binding checks; see [agent-service.md](agent-service.md#client-commands).
The optional native startup hooks provide local context only. They do not
prepare a fresh clone, verify anything or grant merge authority; automatic
execution requires the runtime's exact-definition trust review.

Follow the ownership contract for one owner per gate and coordinator-owned
integration/waiting. Keep long jobs in the coordinator, or await their specific
process/session handles before the worker exits. A queued command is not a
completed gate; transfer pending handles explicitly instead of abandoning them.

Use the [ten-investigation sample](systematic-corpus-loop.md#observing-the-next-ten-investigations)
in the existing handoff. When investigating startup or verification overhead,
include warm/cold state, acquisition/build work, lease waits and reasons for
repeated gates in the linked logs. Compare equivalent inputs and cache states;
warm no-op evidence compares installed artifacts and source revisions, rather
than inferring reuse from exit code zero. Distinguish bookkeeping from installs,
downloads and compilation. Historical timings are observations, not guaranteed
savings or evidence of faster philosophical conclusions.
