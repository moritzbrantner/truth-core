---
name: truth-core-research
description: Advance a bounded philosophical research argument in the truth-core repository, reusing its corpus and Lean evidence and publishing a reviewable result. Use for research workers, not general repository tooling changes.
---

Paths below are relative to the repository root. Work from the coordinator's target, exact reuse, live uncertainty, expected value and bounded return. Read `AGENTS.md` if it is not already loaded; it governs sources, proof boundaries, shared vocabulary, persistence and final verification. Consult the existing investigation/handoff rather than creating a second tracker.

Use the [systematic corpus loop](../../../docs/systematic-corpus-loop.md) as the canonical research method for selecting questions, tactics, priorities and stopping conditions. This skill supplies the bounded worker entry point and handoff, not a separate research strategy.

Follow its [parallel-lane policy](../../../docs/systematic-corpus-loop.md#parallel-lanes): use the brief's frozen semantic baseline and owned checkout/files, and return shared definition or bridge changes to their designated owner. Unaffected independent investigations continue during review and CI. A generalization already supplied by an existing theorem calls for a dependency finding or short reuse lemma.

Work one bounded question with a named root-route purpose. Follow the brief's owned files, effort bound, return condition and authorized outputs. Return early when the question is answered, existing evidence already supplies the result, a semantic or warrant finding changes the next useful step, or a precise obstacle blocks the assigned work. Reaching the effort bound with no result is a valid return; do not invent a theorem, premise or corpus record to fill a quota. Broader follow-up belongs in the coordinator's next brief.

For assigned logic tasks, including the Carneades.org campaign, apply **logic
first, attribution deferred** (owner direction, 2026-11-05). The canonical loop
selects between logic, interpretation and warrant questions. Work from available
summaries, transcripts and explicit analyst propositions; source acquisition and exact author
intentions must not block formalization. Use declared assumptions, interpretation
variants, consequences and countermodels. Do not add source/claim/passage records
by default or start PDF/extractor/source-infrastructure work for a logic task.
Preserve available source leads in existing notes or attempts, marked deferred.
Resume attribution work when the brief selects it within the authorized scope. Proof gates
and truthful source-claim boundaries remain in force.

**Connect the assigned question to the case.** Name the root-route node or explicit bridge the work serves. Use `python3 scripts/corpus.py frontier --routes` for route context and `truth orphans` when disconnected results are relevant to the question. In the return or authorized PR, show the connection in `frontier-diff`, or give the target, missing bridge and blocker. Use the canonical loop to judge priority and whether a fork, semantic investigation or warrant assessment is useful; do not impose an idle-library or exhaustive-fork prerequisite on every worker.

Track senses by label (owner direction, 2026-11-07): each disambiguated term has senses TERM_n (PRIOR_1, PRIOR_2) with uuid identities. Each sense is its own Lean type (`lean_declaration` on the sense), so equivocation is a type error; give a new sense its own declaration, never reuse another sense's. Use one sense per term in each argument; an argument that works in two senses becomes two arguments (`for_each_sense` in the batch spec), and a premise relating two senses is listed in `sense_bridges`. `corpus.py context` and `dossier` show the labels; `corpus.py check` rejects unbridged mixing in new arguments. Coverage and exclusivity are separate claims, required only when the proposed inference needs them; follow the canonical loop and selected configuration tactic for those obligations.

Identity: corpus ids are opaque uuids. Never mint a readable id; give each new record a plain, sense-tagged `label` (`python3 scripts/new_id.py` mints ids, `argument_batch.py` does it for specs). Commands accept a uuid, legacy id (`STMT-…`) or label.

When reconciling an older research branch, compare its records with current main
before replaying commits or restoring a stash. Preserve newer definitions,
disambiguations, module declarations and verified findings. A commit absent from
main's history does not mean its result is absent from the corpus.

For sense and identity work, follow the schema actually present in the selected
checkout. The structure changes are tracked in #1233, with sense indexing in
#1235, opaque record identity in #1240, and recursive formal meaning in #1242.
Once available, use the existing identity resolver and batch generator: reuse
migrated UUIDs and their legacy aliases, give new records UUIDs and human labels,
and preserve sense UUIDs independently of display labels. Do not recreate an
existing result under a fresh identity or treat a label as its meaning.

For each load-bearing word, inspect the definition body and its consequential
terms recursively, reusing existing vocabulary. Distinguish explicit primitives
and their open interpretation obligations from completed definitions. Distinct
names or Lean constants alone do not establish distinct meanings. Keep contested
bridges as explicit propositions rather than hiding them in definitions.
Where the sense schema is available, declare the argument's selected senses,
use separate arguments for separate readings, and register an actual premise or
conclusion bridge when moving between them. Check that bound hypotheses and the
conclusion instantiate the intended sense, including predicate parameters.
Legacy allowlisting records unfinished work; it is not evidence of successful
sense binding. Keep the existing frozen Challenges and certification boundaries.

Inventory before formalization: for an existing target argument run `python3 scripts/corpus.py context <ARGUMENT-OR-RESULT-ID>`, then inspect each touched premise's `python3 scripts/corpus.py dossier <STMT-ID>`, then exact existing definitions, theorem types and recorded attempts. Prefer a concrete rival model or a consequential bridge test over another general-purpose distinction. Coordinate a genuinely new shared definition with its designated owner; submit independent proof edits directly yourself.

Keep these outcomes distinct in records and the return:

- **Formal consequence:** the exact claim, assumptions and semantics, with its theorem or model evidence and checks completed or pending.
- **Source and semantic fidelity:** whether the source reading and formal interpretation capture the intended content, with alternatives and open interpretation burdens.
- **Independent warrant:** reasons for accepting or doubting the premises or their application, including serious objections and unanswered bridges.
- **Work completion:** whether the bounded question was answered, redirected, blocked or exhausted its budget without a result. This does not assign a proposition's proof status.

An overall provisional judgment may guide priorities and support qualified philosophical conclusions. State its evidence, assumptions, uncertainty, strongest surviving rivals and what would revise it in the existing note or handoff. Keep it revisable; it does not establish or refute a proposition formally, supply a missing certificate, or close a frontier premise.

For Lean development, use the coordinator's existing local service and preview identity when supplied. Do not start a service/session or repeat preparation. From your canonical clone, submit full source content:

```bash
python3 scripts/agent_lean.py path/to/Edit.lean \
  --workspace "$PREVIEW" --session "$SESSION" --path Scratch/my-task/Edit.lean
```

Use the supplied endpoint through `--url` when it differs from the local default; `--goal LINE CHARACTER` uses zero-based positions. The helper holds the shared lease, rejects mismatched revision/workspace/session/content bindings, reports lease wait separately, and returns nonzero for Lean errors. Exit 0 can still include `sorry` warnings; inspect diagnostics, and use unfinished goals during development. Keep its JSON evidence, including preview HEAD and content hash, alongside your canonical revision. A clean preview is not final verification. If the helper rejects a changed preview HEAD, obtain the coordinator's current dependency/setup information; do not refresh or rebuild the shared preview yourself. See `docs/agent-service.md` for configuration and CLI fallback.

When no usable local service is supplied, continue through the existing CLI with the coordinator's prepared toolchain/cache setup, using `python3 scripts/worker_env.py -- <command> <args...>`. Keep existing ownership and heavy-job locking rules; a service is not a prerequisite for research and the CLI preserves the same final verification requirements.

When the brief selects source work, use the existing materialize command and read the verified passage plus context before attribution. Before the first push, run `python3 scripts/corpus.py attribution-check --base <merge-base> --materialize`; a logic-only PR with no changed stating claims should have nothing to materialize. Give every deliberately added or changed stating claim an `attribution` ("The passage states X, which is the premise."). Where that sentence would be false, defer the attribution or use a `supports` relation with a gap note (#987). Do not repair acquisition or extraction infrastructure merely to publish a logical result: keep the analyst proposition and defer new attribution/witness records. Keep rival readings and open commitments explicit. A source's assertion, a typed conditional and an independently defended premise are different evidence.

For newly introduced or substantially reinterpreted causal, dependency, grounding, contingency, necessity or explanatory relations, follow `AGENTS.md` and the [semantic grounding questions](../../../docs/systematic-corpus-loop.md#semantic-grounding-of-metaphysical-relations): meaning, examples/counterexamples (or their unavailability), exclusions, independently justified properties, the abstraction bridge, and serious competing accounts. Prioritize properties and abstraction; persist answers and explicit **OPEN** burdens in existing definitions/disambiguations or linked notes. Conditional relational proofs may proceed, but do not establish applicability or discharge those burdens.

Before handoff, preserve substantive findings, failed approaches, precise locators and remaining bridges in the existing corpus records/linked notes and attempts. Return the exact question and scope, findings or no result, evidence and verification status, actual premise effects, remaining gaps and recommended next step. Include the revision and changed paths, plus the PR/head and pending CI or job identity when present. A useful return can consist of a reuse finding, semantic clarification, warrant assessment or a documented unsuccessful search without a new theorem or PR.

For changed claims, statements, arguments or results, complete one claim/type self-sweep, including what every model actually witnesses and the exact root-premise comparison. Consequential findings need the canonical [semantic challenge](../../../docs/systematic-corpus-loop.md#independent-semantic-challenge) on their final claims and evidence, including omitted commitments and open interpretation bridges. Reuse successful checks when their inputs and dependencies are unchanged; final delivered-head CI retains its required coverage. When the brief authorizes publication, group the reviewable work in one coherent direct-main PR with the actual assumptions and remaining gaps. Before an authorized push, merge fresh main and regenerate the imports/docs; request the required current-head review once. A PR is not mandatory for every bounded worker. Merge authority remains whatever the user and current brief authorize.
