# Systematic corpus loop

Advance substantial arguments toward the [root goal](https://github.com/moritzbrantner/truth-core/issues/143), not statement or theorem counts. Constraint discovery within frontier investigations leads; source campaigns serve decisive gaps. `AGENTS.md` governs source fidelity, Lean/Comparator verification, and review.

## Frontier investigations: argument-first, decomposition on demand

For one owner-scoped thesis or argument (#565):

1. **Map the whole case.** State the conclusion and downstream purpose, strongest positive argument and serious rivals, existing statement/theorem IDs, explicit assumptions, and current bottleneck.
2. **Verify the conditional structure.** Formalize load-bearing inferences and test omissions or rival models. A verified implication does not establish its premises.
3. **Force choices before expanding premises.** Follow the [certified fork workflow](configuration-elimination-loop.md#certified-forks-as-the-default-frontier-workflow): compose implications, certify incompatible bundles, prove coverage of substantive branches, and seek models of survivors under a fixed background. Investigate a child premise only when its resolution would discriminate those branches; do not default to another layer of assumptions.
4. **Decompose on demand.** Separate canonical statements/tasks only when inference, a real disagreement, independent justification, reuse, or a source/proof invariant requires it. Do not manufacture atomized taxonomies or duplicate issues.
5. **Recompose immediately.** Connect the child's actual result to its parent, update unresolved assumptions and alternatives, and continue the same argument. A failed route yields a recorded countermodel or precise blocker, not a stronger invented premise.

Keep the readable case and rivals in its existing issue/note; keep proofs, sources, countermodels, and substantive attempts in their canonical records/dossiers. No parallel research registry. The [#565 pilot note](notes/argument-first-pilots-565.md) illustrates the method with #564 and #563.

## Progress is depth on the root path, not volume

Use `python3 scripts/corpus.py frontier --routes` and `--reaching-root`. Report exactly what changed for root-facing open premises, including **no change** for unconnected outposts.

- An open premise is **bare** (no source claim/support) or **sourced but undefended**. First remove bare gaps, then independently defend sourced premises.
- A transcription (`opaque_atoms`, `single_application`, `assembly`, `instantiation`) does not close an open conclusion; it propagates closure only when **all** its premises are closed. An alleged refutation counts only when verified **and** all its premises are closed.
- Replacing one open premise with narrower leaves ("relocation") counts as progress only when **every** new leaf is sourced **and** needed by an omission countermodel.
- Neither source attribution, a conditional theorem, a narrative, nor an unverified model proves a premise. Preserve exact semantics, assumptions, and surviving rivals; see [configuration elimination](configuration-elimination-loop.md).

## 1. Campaign: a meaningful source objective

A coarse GitHub issue names a coherent source objective and completion criteria; it is not a second status tracker. Choose source reading when a live argument needs that evidence, not just to grow coverage.

## 2. Candidate: the next contiguous source range

`corpus/candidates/*.json` queues chapter-sized or similarly coherent ranges. Use `python3 scripts/corpus.py next` when doing source ingestion:

1. Materialize the verified witness; read the whole range and context before splitting it.
2. Proceed in source order. Record substantive readings and inferential steps, reuse existing identities, and preserve defensible alternatives. Skip filler; not one claim per sentence.
3. Apply the atomic research/proof contract in `AGENTS.md`. Keep the same candidate and advance its locator after a partial batch; delete it only when its range is exhausted.

## PR boundary

Ship one coherent verified argument cluster, a complete candidate range, or a reviewable part of it (about 5–10 claims at most, not a quota). Report premise effects and remaining gaps; persist substantive failed attempts before handoff. A PR boundary does not end the investigation.

## Parallel lanes

Follow the A/B/C ownership in `AGENTS.md` (#416). Shared Lean imports and documentation tables are generated, never hand-edited; rerun `scripts/root-imports.sh --write` and `python3 scripts/docs_index.py --write` after merging `origin/main` before pushing.

## Completion and coverage

A source range is complete once read and its relevant substantive content represented or explicitly judged out of scope; it need not generate a claim for every sentence. A frontier slice ends only when its conclusion is established under the stated standards, the route is decisively defeated, or a precise obstacle requires owner judgment. A conditional result with open premises is not established.

## Failed proofs feed research

Record the missing premise and strongest countermodel, not an added axiom or stronger source reading. First test whether the failure exposes a countermodel, incompatible bundle or useful fork. Pursue a targeted child argument or source candidate when it can resolve that fork; do not automatically expand the premise queue.

## Campaign handoff

When a campaign finishes, follow its known successor, seed its first source-range candidate, then close it. Keep one current handoff. Stop only for genuinely unavailable evidence, a scope/modeling choice requiring the owner, a repository defect, or an ambiguous successor.

## Campaign ordering

Prioritize the active frontier slice and its blockers; source campaigns follow those needs. Within a campaign, finish the current range, backfill necessary foundations, then continue the source while useful. The original Aristotle `Physics` III → I–II → IV–VIII order remains a fallback, not a competing global priority.
