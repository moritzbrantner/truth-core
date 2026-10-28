---
name: truth-core-research
description: Advance a bounded philosophical research argument in the truth-core repository, reusing its corpus and Lean evidence and publishing a reviewable result. Use for research workers, not general repository tooling changes.
---

Paths below are relative to the repository root. Work from the coordinator's target, exact reuse, missing step and premise comparison. Read `AGENTS.md` if it is not already loaded; it governs sources, proof boundaries, shared vocabulary, persistence and final verification. Consult the existing investigation/handoff rather than creating a second tracker.

Inventory before formalization: inspect each touched premise's `python3 scripts/corpus.py dossier <STMT-ID>`, then exact existing definitions, theorem types and recorded attempts. Prefer a concrete rival model or a consequential bridge test over another general-purpose distinction. Coordinate a genuinely new shared definition with its designated owner; submit independent proof edits directly yourself.

For Lean development use the coordinator's existing local service and preview identity. Do not start a service/session or repeat preparation. From your canonical clone, submit full source content:

```bash
python3 scripts/agent_lean.py path/to/Edit.lean \
  --workspace "$PREVIEW" --session "$SESSION" --path Scratch/my-task/Edit.lean
```

Use the supplied endpoint through `--url` when it differs from the local default; `--goal LINE CHARACTER` uses zero-based positions. The helper holds the shared lease, rejects mismatched revision/workspace/session/content bindings, reports lease wait separately, and returns nonzero for Lean errors. Exit 0 can still include `sorry` warnings; inspect diagnostics, and use unfinished goals during development. Keep its JSON evidence, including preview HEAD and content hash, alongside your canonical revision. A clean preview is not final verification. If the helper rejects a changed preview HEAD, obtain the coordinator's current dependency/setup information; do not refresh or rebuild the shared preview yourself. See `docs/agent-service.md` for configuration and CLI fallback.

For source work use the existing materialize command and read the verified passage plus context before attribution. Keep rival readings and open commitments explicit. A source's assertion, a typed conditional and an independently defended premise are different evidence.

Before using causal/dependency relations as metaphysical support, follow the [five interpretation questions](../../../docs/systematic-corpus-loop.md#interpreting-causal-and-dependency-relations): meaning, actual examples, exclusions, independently justified properties, and the physical-to-metaphysical abstraction bridge. Prioritize the last two; persist answers and explicit **OPEN** burdens in existing definitions/disambiguations or linked notes. Conditional relational proofs may proceed, but do not establish applicability or discharge those burdens.

Before handoff, preserve findings, failed approaches, precise locators and remaining bridges in the existing corpus records/linked notes and attempts. Complete one claim/type self-sweep, including what every model actually witnesses and the exact root-premise comparison. Merge fresh main before push and regenerate the imports/docs. Reuse successful checks when their inputs and dependencies are unchanged; final delivered-head CI retains its required coverage. Publish one coherent direct-main PR with the actual assumptions and remaining gaps, request the required current-head review once, and return the PR/head plus pending CI identity to the coordinator. Merge authority remains whatever the user and current brief authorize.
