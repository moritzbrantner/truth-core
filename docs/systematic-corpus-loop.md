# Systematic corpus loop

The corpus should advance through philosophical works without requiring a human to nominate each sentence. The repository therefore uses two nested scales of work.

## 1. Campaign: a meaningful source objective

A GitHub issue may represent a campaign such as **Aristotle, Physics III**. A campaign is deliberately coarse. It can take several PRs and it should describe the source boundary and completion criteria, not maintain its own workflow state machine.

Campaigns are useful for choosing *where the project is going*. They are not the canonical store for claims, propositions, or proofs.

## 2. Candidate: the next contiguous source range

`corpus/candidates/*.json` is the lightweight execution queue. A candidate should usually cover a chapter or another coherent source range, not one sentence and not one already-decided proposition.

Run:

```bash
python3 scripts/corpus.py next
```

The selected worker owns that range until it has either exhausted it or reached a reviewable PR boundary.

### Range processing

Within a candidate:

1. Read the whole range and enough surrounding context to understand its argumentative shape.
2. Process the text in source order.
3. Extract only philosophically substantive propositions, distinctions, definitions, premises, conclusions, objections, replies, and explicit inferential moves.
4. Skip purely connective, rhetorical, repetitive, editorial, or example-only sentences unless they materially constrain an interpretation.
5. For each extracted reading, apply the atomic worker contract in `AGENTS.md`.
6. Preserve competing defensible readings rather than forcing one.
7. Reuse existing statements only after checking semantic identity.

This makes the unit of scholarship atomic while keeping the unit of agent execution large enough to make continuous progress.

## PR boundary

Prefer a PR when one of these is true:

- the candidate range is complete;
- roughly 5–10 new source claims have been formalized;
- one coherent argument cluster and its verification are complete; or
- the next passage requires a materially different formal vocabulary or research question.

A PR boundary is not a reason to ask the human what sentence comes next.

If the candidate still has unprocessed text, update the same candidate file so its locator begins at the first unprocessed passage. Keep its ID. After merge, the next worker resumes it with `corpus.py next`.

If the candidate is complete, delete the candidate file. The next queued source range then becomes active automatically.

## Completion and coverage

A source range is complete when the worker has read it in full and either:

- represented every philosophically substantive reading needed for the current corpus scope; or
- explicitly determined that remaining text is expository, repetitive, or not yet useful enough to justify a new claim.

Completeness does **not** mean one claim per sentence. It means no substantive passage was silently skipped.

For an existing claim in the range, review and reuse it rather than duplicating it. This allows systematic passes over books that already contain seed claims.

## Failed proofs feed research

A failed proof does not justify strengthening a source claim. If an advertised argument needs a substantive premise that has not been formalized, add a candidate for the best source location to investigate. Give it a higher priority than routine forward reading when it blocks an argument already in the corpus.

This is the main feedback path from proof work back into source work.

## Campaign handoff

The queue should replenish itself across campaigns as well as inside them.

Before closing a completed campaign:

1. follow any explicit successor campaign already named in the issue or repository guidance;
2. ensure that successor campaign exists as a coarse issue when useful;
3. seed at least its first chapter/range candidate so `python3 scripts/corpus.py next` has work immediately;
4. then close the completed campaign.

Do not ask the human to restart the loop when the successor is already determined. Escalate only when choosing the next work or philosopher is a genuine scope decision that the documented ordering and existing proof dependencies do not resolve.

## Campaign ordering

Prefer depth before breadth:

1. finish the current contiguous campaign;
2. backfill nearby foundational material that the campaign repeatedly depends on;
3. continue through the same work while the vocabulary remains useful;
4. only then open a new work or philosopher, unless a proof dependency gives a concrete reason to branch.

For the current seed corpus, the immediate campaign is Aristotle's `Physics` III, continuing immediately after the existing 201a10–11 change definition. The initial queue covers the remainder of III.1 and then III.2–III.8 in chapter order. Existing campaign tickets then order the Physics I–II backfill before continuing through Physics IV–VIII.
