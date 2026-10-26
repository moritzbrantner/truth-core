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

## Progress is depth on the root path, not volume

The repository's aim (#143) is a graph from the root statement "Catholicism is true" (#156) down to premises that are either self-evident or whose alternatives are all refuted. Progress is measured as **load-bearing frontier nodes closed on paths to that root**, as reported by `python3 scripts/corpus.py frontier`. Claim counts, result counts, and source coverage are not progress measures.

In practice:

- choose work from the frontier, preferring open premises that many arguments depend on or that objections attack, and agree on the direction with the owner at each milestone;
- a transcription result (AGENTS.md invariant 16) closes no frontier node by itself. It closes its conclusion only when every premise of its argument is closed: marked self-evident, defended by refuting every recorded alternative, the conclusion of a verified non-transcription result, or closed by this same rule. `corpus.py frontier` computes this as a fixpoint and lists such nodes as `closed via transcription from closed premises` (owner decision on #143, 2026-10-24). A transcription that has an open premise, typically its bridge premise `A ∧ B → C`, still closes nothing. A result is a transcription when its record declares one in the structured `transcription` field (`opaque_atoms`, `single_application`, `assembly` or `instantiation`), or when its proof is a single application of one hypothesis or only assembles hypotheses (`⟨hClaims, hRose⟩`). Declare the field on every result whose atoms are unconstrained `Prop` parameters or whose description calls it a transcription; prose in `description` is commentary, not the flag, and `corpus.py check` warns about unflagged opaque-atom candidates (#391);
- a `refutes` relation defends a premise only when its argument is verified and all of that argument's premises are closed (#391). A conditional refutation resting on open premises leaves the alternative standing, and `corpus.py check` warns about it;
- report a PR's effect on the root with `corpus.py frontier --routes`: for each argument concluding the root, the number of its premises that are not established, with the cheapest verified route marked. A new derivation never raises a route's cost, so a relocation that adds open premises under an already-open node shows as "no change" there and as frontier growth in `--reaching-root`;
- a source campaign (e.g. Aristotle's *Physics*) continues only where a premise on a root path depends on it.

### Relocation and the depth of open premises

Replacing one open premise by several narrower ones (a *relocation*) can grow the frontier and still be progress (owner decision on #143, 2026-10-24). It counts as progress when **every** new open premise is:

1. **sourced**: a claim states it, or a `supports` relation points to it from a source claim; and
2. **shown necessary** by a countermodel: a Lean model that satisfies every other premise of the argument but falsifies the conclusion once that premise is dropped.

`corpus.py frontier` therefore classifies each open premise by depth:

- **bare**: no claim states it and no `supports` relation points to it;
- **sourced** (sourced but undefended): a claim states it or supports it, but it is not yet closed (proved, self-evident, or defended by refuting every recorded alternative).

The summary line reports both counts, e.g. `frontier: 28 open premises: 8 bare, 20 sourced-undefended`; `--json` gives `depth_counts` and a `depth` per item, and `/graph` tags open premises `frontier:bare` or `frontier:sourced`. The aim is to drive bare premises to zero first, then defend the sourced ones.

This rule exists because the earlier corpus optimized what it counted: about 100 mostly one-step results in three days, then the campaign stalled.

## PR boundary

The thresholds below are an upper size bound for reviewability, not a quota. Fewer, deeper results are better than many shallow ones.

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

Since 2026-10-23 the frontier of the root graph (#143, #156) takes precedence over source campaigns. The ordering below applies only within a campaign that a root path currently needs.

For the original seed corpus, the campaign was Aristotle's `Physics` III, continuing immediately after the existing 201a10–11 change definition. The initial queue covers the remainder of III.1 and then III.2–III.8 in chapter order. Existing campaign tickets then order the Physics I–II backfill before continuing through Physics IV–VIII.
