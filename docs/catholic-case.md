# The Catholic case: program, decisions, and working method

This document is the durable handoff for the campaign tracked in epic #143. It records what the owner decided and how the work is run, so that a new session on any machine can continue without the previous session's local notes. The current snapshot of open work lives in the latest "Handoff" comment on #143. GitHub issues and PRs remain the work state.

## Goal

Formalize the case that Catholicism is true as a graph of source-grounded Lean 4 propositions. From the root `STMT-CATHOLICISM-TRUE`, every path should end in premises that are either self-evident or whose alternatives are all shown false or contradictory. Rival worldviews and objections are refuted along the way.

Lean verifies **consequence**, not premise truth. Premise truth is defended by further sourced arguments, never by axioms (`permitted_axioms: []` everywhere).

## Root and structure

- **Root (phase 1, #156/#159):** `STMT-CATHOLICISM-TRUE` := (A) the Catholic Church is the teaching authority founded by God (Vatican I, *Dei Filius* ch. 3, pinned on vatican.va in #170) ∧ (B) the twelve articles of the Nicene–Constantinopolitan Creed (Greek, `CREED-C381`).
- **Phase 2 (later):** the full list of defined dogmas (Ott, Denzinger), candidate `CATHOLICISM-ROOT-PHASE-2-DOGMAS`.
- **Skeleton:** the root ⇐ six stages plus explicit bridges (`TruthCore/Results/Case/Catholicism/Skeleton`):
  1. God exists
  2. classical attributes
  3. revelation possible and recognizable
  4. Jesus' claims and the Resurrection
  5. Christ founded a visible Church
  6. that Church is the Catholic Church
- Unproved stages are open premises, never axioms.
- **Refutation track:** objections and rival worldviews (atheist and naturalist, other religions, Protestant and Orthodox positions).

## Owner principles (binding)

| Date | Principle | Where recorded |
|---|---|---|
| 2026-10-23 | Classical Thomistic order, continuously expanded to show objections and alternatives false. | #143 |
| 2026-10-23 | Historical stages 4–6: no minimal-facts case. Build a cohesive Catholic worldview and compare it with rival theories as **whole systems**. Historical findings are explicit sourced premises. No Bayesian or probabilistic machinery. | #143 |
| 2026-10-23 | **No win by subtraction.** A rival is a complete worldview answering the same shared question set. Denying a premise counts only together with a replacement account. "Unknown" is allowed but recorded as *unexplained*. | #143 |
| 2026-10-23 | A theory is a set of propositions and arguments plus an **answer map** (question → proposition or "unexplained"). Results are presented as **counts plus prose**, never an aggregate score. Historical findings are pinned to historical-source-atlas **without certainty numbers**; competing theories are investigated instead. | #149 |
| 2026-10-23 | **Premise program.** Every premise ends either *self-evident* (itself an argued, sourced claim) or with *all alternatives refuted*. | #143 |
| 2026-10-23 | **Problem of evil, primary angle:** rivals must ground *objective* good and evil (the Q-MORAL-GROUNDING dilemma). Also required: the consistency of Catholic theism with evil, which answers the internal-critique form. | #150, #160 |
| 2026-10-23 | YouTube debates are admissible sources (`media_span`, #152). Translations are used where no pinned Latin witness exists (`web_snapshot`, #154). | #143 |
| 2026-10-23 | Expansion strategy: skeleton first, then the frontier. Agree the direction with the owner at each milestone. | #156 |
| 2026-10-23 | Depth over volume (AGENTS.md invariants 16–19): a transcription is not a proof; compose, don't restate; source kinds are frozen; truth-core is self-sufficient. | #158 |
| 2026-10-24 | Frontier closure: a transcription closes its conclusion only when **all** of its premises are closed. | #172 |
| 2026-10-24 | **Relocation counts as progress** when every new premise is sourced and shown necessary by a countermodel. The frontier distinguishes *bare* from *sourced but undefended* premises. Drive bare premises to zero first. | #143, #175 |
| 2026-10-24 | `STMT-MAXIME-ENS-IS-GOD` is to be closed via the **uniqueness of the maximum in being** plus an explicit, sourced nominal definition. | #143 |
| 2026-10-24 | Intuitionist withholding of excluded middle: first Aristotle's remaining *Metaphysics* IV.7 arguments, then intuitionism as a complete rival worldview. | #143, #174 |

## Modeling decisions worth knowing

- **First Way (#151):** strong per se reading ("moved by none in any respect") plus a weaker sibling reading; an interpretive argument that the strong reading is Thomas' meaning. The conclusion is double-negated (`¬¬∃`), so excluded middle is an explicit premise.
- **Excluded middle (#169):** a single general principle `STMT-EXCLUDED-MIDDLE`, marked `self_evident`, argued from Aristotle's elenchus and from constructive Lean results that refute *denial*. Intuitionist *withholding* is recorded as an alternative that is not yet refuted.
- **Stage-1 gap (#166, #173):** pure act, simplicity and uniqueness are derived. The identification with God is relocated to narrower open premises such as `STMT-MAXIME-ENS-IS-GOD` and `STMT-SIMPLY-PRIOR-IS-CAUSE-OF-BEING`. Countermodels show each premise is needed.
- **Graph integrity:** `corpus.py bind-check` (#164) verifies in CI that each argument's JSON premises and conclusion are exactly the Lean theorem's hypotheses and result type. Theory bundles are unfolded one step (#160).
- **Visualization:** `apps/corpus-explorer` `/graph` (#163). Run `cd apps/corpus-explorer && bun run dev`, then open http://localhost:3000/graph/.

## Working method

- **One coordinator plus background workers**, one git worktree per worker, created from `origin/main`.
  - Each worker gets a self-contained brief: issue, invariants, checks, process.
  - The coordinator relays owner decisions and records them on #143.
- **CI.** GitHub Actions do not start on this private repo (billing). Run every job in `.github/workflows/ci.yml` locally and post "local CI run for <sha>: …" on the PR. A green local run counts as the check.
- **Review and merge.**
  - Request one targeted `@codex review` per PR, plus at most one re-request when a review hangs or after real P1 fixes. Fix real P1s only.
  - Merge with plain `gh pr merge --squash` only after a **completed** review with no open P1 whose reviewed commit is the head (or only trivially rebased).
  - Never use `--admin`. Never merge without a completed review; #158 was the one exception, kept by owner decision.
- **Memory-constrained machines.** Wrap heavy commands (`lake build`, `verify-*`, `bun install`, `next build`, `source_evidence.py verify`) in `flock /tmp/<user>/truth-core-heavy.lock` and keep build parallelism low.
- **Fresh machine setup.**
  - Install `elan` (toolchain from `lean-toolchain`), Go, Bun and Python 3.
  - Run `scripts/bootstrap-verifier.sh`, which builds the Comparator, lean4export, landrun and NanoDa into `~/.cache/truth-core-verifier`.
  - Media spans also need a youtube-corpus export (see `docs/source-evidence.md`).

## Owner to-dos

- Audio-check the six O'Connor spans (speaker and wording) — #168.
- Decide whether to archive `proposition-api`. Its claim-extraction ownership was decided on 2026-10-13; the retrospective found its extraction to be a regex heuristic.

## Lessons from earlier attempts (2026-10-23 retrospective)

- **Schema and infrastructure before content.** truth-engine went through about 10 schema versions in 15 days, and its solver services had no real workload. They are archived.
- **Decorative formalization.** Opaque `Prop` atoms with the conclusion inside a bridge premise: about 84 of 103 Aristotle results are 1–2-line transcriptions.
- **Volume metrics.** About 100 results in 3 days, then a stall.
- **The rule that follows:** progress means load-bearing nodes closed on root paths, measured by `python3 scripts/corpus.py frontier --reaching-root`.
