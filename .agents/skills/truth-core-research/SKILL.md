---
name: truth-core-research
description: Advance a bounded philosophical research argument in the truth-core repository, reusing its corpus and Lean evidence and publishing a reviewable result. Use for research workers, not general repository tooling changes.
---

Paths below are relative to the repository root. Work from the coordinator's target, exact reuse, missing step and premise comparison. Read `AGENTS.md` if it is not already loaded; it governs sources, proof boundaries, shared vocabulary, persistence and final verification. Consult the existing investigation/handoff rather than creating a second tracker.

The current phase is **logic first, attribution deferred** (owner direction,
2026-11-05). Prioritize the Carneades.org arguments. Work from available summaries,
transcripts and explicit analyst propositions; source acquisition and exact author
intentions must not block formalization. Use declared assumptions, interpretation
variants, consequences and countermodels. Do not add source/claim/passage records
by default or start PDF/extractor/source-infrastructure work for a logic task.
Preserve available source leads in existing notes or attempts, marked deferred.
Only resume attribution work when the owner explicitly selects it. Proof gates
and truthful source-claim boundaries remain in force.

**Connect to the case first (owner direction, 2026-11-07).** Never build or extend a library, framework or vocabulary that no root route uses. Before choosing work:
- Run `python3 scripts/corpus.py frontier --routes` and list the verified result families that do not reach `STMT-CATHOLICISM-TRUE` (`truth orphans`). A large disconnected family, such as the modal library that the necessary-being routes ignored, is the first thing to connect.
- Name the root-route node your work serves.
- In the PR, show the connection in `frontier-diff`, or give an explicit connection plan with its blocker.
- For a load-bearing ambiguous term, first add the COVERAGE premise ("these are all the relevant senses") and the EXCLUSIVITY premise ("exactly one applies"). Then make a typed sense enum, a result per sense (or a countermodel), and a joint theorem by cases. Only then attack rival definitions.

See AGENTS.md, "Connect every library to the case".

Identity: corpus ids are opaque uuids. Never mint a readable id; give each new record a plain, sense-tagged `label` (`python3 scripts/new_id.py` mints ids, `argument_batch.py` does it for specs). Commands accept a uuid, legacy id (`STMT-…`) or label.

Inventory before formalization: for an existing target argument run `python3 scripts/corpus.py context <ARGUMENT-OR-RESULT-ID>`, then inspect each touched premise's `python3 scripts/corpus.py dossier <STMT-ID>`, then exact existing definitions, theorem types and recorded attempts. Prefer a concrete rival model or a consequential bridge test over another general-purpose distinction. Coordinate a genuinely new shared definition with its designated owner; submit independent proof edits directly yourself.

For Lean development use the coordinator's existing local service and preview identity. Do not start a service/session or repeat preparation. From your canonical clone, submit full source content:

```bash
python3 scripts/agent_lean.py path/to/Edit.lean \
  --workspace "$PREVIEW" --session "$SESSION" --path Scratch/my-task/Edit.lean
```

Use the supplied endpoint through `--url` when it differs from the local default; `--goal LINE CHARACTER` uses zero-based positions. The helper holds the shared lease, rejects mismatched revision/workspace/session/content bindings, reports lease wait separately, and returns nonzero for Lean errors. Exit 0 can still include `sorry` warnings; inspect diagnostics, and use unfinished goals during development. Keep its JSON evidence, including preview HEAD and content hash, alongside your canonical revision. A clean preview is not final verification. If the helper rejects a changed preview HEAD, obtain the coordinator's current dependency/setup information; do not refresh or rebuild the shared preview yourself. See `docs/agent-service.md` for configuration and CLI fallback.

When the owner explicitly selects source work, use the existing materialize command and read the verified passage plus context before attribution. Before the first push, run `python3 scripts/corpus.py attribution-check --base <merge-base> --materialize`; a logic-only PR with no changed stating claims should have nothing to materialize. Give every deliberately added or changed stating claim an `attribution` ("The passage states X, which is the premise."). Where that sentence would be false, defer the attribution or use a `supports` relation with a gap note (#987). Do not repair acquisition or extraction infrastructure merely to publish a logical result: keep the analyst proposition and defer new attribution/witness records. Keep rival readings and open commitments explicit. A source's assertion, a typed conditional and an independently defended premise are different evidence.

For newly introduced or substantially reinterpreted causal, dependency, grounding, contingency, necessity or explanatory relations, follow `AGENTS.md` and the [semantic grounding questions](../../../docs/systematic-corpus-loop.md#semantic-grounding-of-metaphysical-relations): meaning, examples/counterexamples (or their unavailability), exclusions, independently justified properties, the abstraction bridge, and serious competing accounts. Prioritize properties and abstraction; persist answers and explicit **OPEN** burdens in existing definitions/disambiguations or linked notes. Conditional relational proofs may proceed, but do not establish applicability or discharge those burdens.

Before handoff, preserve findings, failed approaches, precise locators and remaining bridges in the existing corpus records/linked notes and attempts. Complete one claim/type self-sweep, including what every model actually witnesses and the exact root-premise comparison. Merge fresh main before push and regenerate the imports/docs. Reuse successful checks when their inputs and dependencies are unchanged; final delivered-head CI retains its required coverage. Publish one coherent direct-main PR with the actual assumptions and remaining gaps, request the required current-head review once, and return the PR/head plus pending CI identity to the coordinator. Merge authority remains whatever the user and current brief authorize.
