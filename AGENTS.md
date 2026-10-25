# Codex worker contract

This repository grows one small source reading or argument at a time. Keep the complexity in the philosophy, not in repository machinery.

## Worker brief and handoff

The master gives each worker a four-line brief:

1. **Target:** the skeleton node, argument or root obligation advanced.
2. **Reuse:** the existing statement IDs and exact Lean theorems to consume.
3. **Missing step:** the inference or source reading still needed.
4. **Premise comparison:** the expected premises retained, added or removed, and whether the work connects results or discharges an obligation.

The PR reports the actual premise comparison, including remaining open premises; a new connection is not itself a discharge. For non-proof work, use “none” or “no premise change” where applicable.

Before handoff or retirement, persist verified source findings, rejected interpretations with reasons, and remaining gaps in the existing passage, claim, definition, disambiguation or candidate records, or their linked repository notes. Keep precise witness locators and distinguish sourced readings from open commitments; temporary files must not be the only copy. Do not create claims merely to record research activity.

## Proof-seeking stance

- Seek machine-checkable consequence, not prose approval. An LLM may propose readings, propositions, formalizations, or proof steps, but its agreement is never evidence that a conclusion follows.
- Use Curry–Howard as the default mental model for formal work: propositions correspond to types and proofs to terms/programs; implication is a function type, conjunction a product, disjunction a sum, and quantified propositions may require dependent function or pair types.
- When claiming `P1, ..., Pn ⊢ C`, make the premises, definitions, and inference rules explicit and reduce the claim to a mechanically checkable artifact, using Lean by default in this repository.
- Keep source interpretation, proposition extraction, formalization, proof search, and proof verification distinct. Lean's kernel verifies accepted proof terms; tactics, solvers, and LLMs are search helpers, not authorities.
- Machine-checkable does not mean automatically discoverable. Failure to find a proof is not a refutation, and formal verification establishes consequence only inside the encoded system—not premise truth, source fidelity, empirical truth, or completeness of the chosen logic.

## Permanent invariants

1. **Research before formalization.** Every source-derived claim must point to a stable source record and a precise locator.
2. **Materialize, do not remember.** Before formalizing a source-derived claim, resolve or create its `corpus/passages/` witness and run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>`. Read that verified text and enough context to interpret it. Model memory, a search snippet, or a plausible citation is never source evidence.
3. **Source integrity is not source fidelity.** A pinned revision, Git blob hash, CTS path, and successful materialization establish which source text was consulted. They do not establish that an interpretation is correct. Preserve that scholarly judgment separately.
4. **Statements have independent identity.** A statement is a proposition used by logic. A claim says that a source supports a statement under an interpretation. Never make statement identity depend on source provenance.
5. **One defensible reading per claim.** If two materially different interpretations are both reasonable, create two claims. They may point to distinct statements even when later work could relate those statements.
6. **Do not merge by similarity.** Textual identity, translation equivalence, formal equality, logical equivalence, philosophical equivalence, and historical identity are different possible relations. Add relations later; do not silently merge statement IDs.
7. **Reuse before invention.** Search existing statements and Lean declarations before adding vocabulary. Reuse only when the meanings genuinely coincide; a false identification is worse than a duplicate statement.
8. **Weakest faithful formalization.** Do not strengthen a source passage to make later arguments easier.
9. **No premise smuggling.** A proof worker may not add an axiom, assumption, definition, or stronger reading solely because a proof needs it. Create a new candidate and source it instead.
10. **Inference is explicit.** Arguments connect statement IDs through inference-application records. Never encode a logical step as an overloaded bare statement-to-statement edge.
11. **Global cycles are allowed; circular proof is not.** Semantic relations and mutually supporting statements may form cycles. Each advertised argument must still be grounded in its premises and mechanically checked by Lean/Comparator.
12. **Challenge is frozen before solution work.** Never weaken or otherwise edit a Challenge merely to make the Solution pass. If source review changes the statement, treat that as a new/revised claim first.
13. **Formal verification is not source verification.** A result verifies an argument's formal consequence. It does not establish that a source really meant a statement or that a premise is philosophically true.
14. **Prefer core Lean.** Add external Lean dependencies only when a philosophical formalization actually needs them.
15. **Do not build identity infrastructure early.** No graph database, RDF ontology, embedding-based merger, or canonical-equivalence resolver until the corpus creates a concrete need. The typed JSON records are sufficient for now.
16. **A transcription is not a proof.** A result whose proof only applies a premise whose consequent already is the advertised conclusion (`exact hBridge ⟨…⟩`), or whose atoms are opaque `Prop`s that nothing constrains, certifies only that "therefore" was transcribed. Such a result may still be recorded as a faithful map of a source argument, but the PR and the result record's description must call it a transcription. It does not count as progress on the case and closes no frontier node by itself (see `docs/systematic-corpus-loop.md`). The one exception is closure carried through it: a transcription closes its conclusion exactly when **every** premise of its argument is already closed—self-evident, alternatives all refuted, the conclusion of a non-transcription result, or itself closed by this same rule (computed as a fixpoint; owner decision on #143, 2026-10-24). A transcription with any open premise, such as an open `A ∧ B → C` bridge, leaves its conclusion open. Where the philosophy has internal structure, formalize that structure with typed vocabulary (beings, respects, causes, sentences, …) so the conclusion is *derived* and the result could have failed.
17. **Compose, do not restate.** Build on earlier results by importing their Lean modules and using their theorems. Do not restate a proved conclusion as a fresh premise. Reuse shared typed vocabulary where meanings coincide (invariant 7); a new per-file `…Reading` vocabulary for a concept the corpus already has needs a stated reason.
18. **Source kinds are frozen.** After `media_span` (#152) and `web_snapshot` (#154), add no new source kind without an owner decision. When a witness cannot be pinned, keep the claim as a candidate marked as waiting for a witness, and continue the reasoning with its statement as an explicit open premise. Sourcing must not block reasoning, and reasoning must not fake sourcing.
19. **truth-core is self-sufficient.** Do not add runtime or CI dependencies on other repositories (historical-source-atlas, worldview-lab, solver services, …). Use one only for a concrete node that is blocked without it, and pin it like a source.

See `docs/corpus-model.md` and `docs/source-evidence.md` for the entity and verification boundaries. For the campaign to formalize the case for Catholicism (epic #143), including the owner's binding principles and the working method, read `docs/catholic-case.md` first.

## Outer systematic loop

The normal operating mode is **not one human prompt per proposition**. A queued candidate represents a contiguous source range, normally a chapter or similarly coherent section. Once an agent starts a candidate, it keeps moving through that range in source order and repeatedly applies the atomic loop below.

1. Run `python3 scripts/corpus.py next` and take the highest-priority candidate.
2. Resolve the candidate range to a pinned source witness. Add the smallest coherent `corpus/passages/` slice if one does not exist, then materialize it and read the complete candidate range before deciding its internal work sequence.
3. Move through the verified source text in order. Extract philosophically substantive propositions and arguments; do **not** create a claim merely because a sentence exists.
4. For every substantive reading, run the atomic research/formalization/proof loop below.
5. Prefer a reviewable batch of roughly 5–10 new source claims, one coherent argument cluster, or the remainder of a short candidate range—whichever boundary comes first.
6. If a batch ends before the candidate range is exhausted, keep the same candidate ID and edit its locator/goal so it begins at the first unprocessed passage. Do not create a second candidate just to represent progress.
7. When the candidate range is exhausted, delete its candidate file. The next run takes the next queued range automatically.
8. When the last candidate of a campaign is exhausted, seed the explicitly ordered successor campaign and its first source-range candidate before stopping. Do not require a human restart when the successor is already determined by repository guidance or an existing campaign issue.
9. Continue without human reprompting unless a stop condition below applies.

A candidate is a queue item, not a philosophical entity and not a ticket-status system. Presence of the file means work remains; deletion means the queued range is complete. GitHub issues may group many candidates into a larger source campaign, and multiple PRs may close one campaign.

### Stop and escalate only for real judgment calls

Do not stop merely because one atomic claim, one PR, or one campaign is finished. Stop the systematic loop only when:

- the primary text or required context cannot be obtained reliably or pinned to an immutable witness;
- two materially different source readings require a human choice about project scope rather than simply preserving both;
- a missing premise points outside the queued source range and choosing the next source is genuinely non-obvious;
- the formal vocabulary would require a cross-cutting modeling decision that changes existing corpus semantics;
- verification exposes a repository/tooling defect rather than a philosophical proof obligation; or
- the enclosing source campaign is complete and choosing its successor remains genuinely ambiguous after applying the documented campaign ordering and existing campaign tickets.

See `docs/systematic-corpus-loop.md` for batching, completion, and campaign guidance.

## One atomic work item

For each philosophically substantive reading or argument encountered inside the current candidate range, perform this loop:

### 1. Research from verified source evidence

- Resolve the passage to a `corpus/passages/` record. Its source snapshot must name the exact edition URN, repository, immutable revision, file path, Git blob SHA, source URL, language, and license. Where no such witness exists, a `web_snapshot` pins a web page by hash instead; claims on a translation carry `basis: translation` (see `docs/source-evidence.md`).
- If no passage witness covers the range, add one from a stable primary-source edition before creating any claim.
- Run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>` and read the materialized text plus enough immediate context to avoid quotation-mining.
- Preserve the conventional classical locator and CTS identity. The conventional locator remains the human citation; the pinned witness makes the consulted bytes reproducible.
- Record a concise paraphrase rather than copying long translations into the repository.
- Identify one atomic source reading or argument.

A worker may use catalogs, translations, commentaries, or search for orientation, but those do not substitute for reading the materialized primary-source witness used by the claim.

### 2. Check reuse

Search `corpus/statements/` and `TruthCore/` for existing propositions and concepts that may express the same thing. Reuse a statement ID only after checking meaning, not merely similar names. When uncertain, preserve separate statement identities; equivalence can be related later.

### 3. Formalize a source reading

- Add the smallest Lean declaration that captures the proposition when a Lean declaration is appropriate.
- Put source locator and interpretation notes in the Lean doc comment.
- Add/update an independent `corpus/statements/*.json` record for the proposition.
- Add/update the corresponding `corpus/claims/*.json` record linking the source reading to that statement.
- Ensure the claim's `source_id` and `locator` resolve to exactly one pinned passage. `python3 scripts/corpus.py check` rejects missing or ambiguous passage evidence.
- Link the senses of load-bearing terms through `definition_ids` and `disambiguation_ids`. When a term or reading choice has no record yet, add a `corpus/definitions/` or `corpus/disambiguations/` record (see Review guidelines and `docs/corpus-model.md`).
- If another reading is also defensible, create a sibling claim with the same source locator and an `interpretation_of` link. Do not use that link to imply statement equivalence.

### 4. Critique fidelity

Before proving anything, explicitly ask:

- Is the formal statement stronger than the source?
- Is it weaker in a way that removes philosophically relevant content?
- Did a natural-language relation get replaced by a modern notion with different semantics?
- Did quantifier scope, modality, time, identity, or causation change?
- Does the cited locator genuinely support this reading when inspected in the pinned passage and its context?

If the answer is materially uncertain, preserve alternatives rather than silently selecting one. A green source-evidence check cannot answer these interpretive questions for you.

### 5. Create an argument only when there is an argument

A source claim need not have a proof: it may simply be a commitment attributed to a text.

When statements are meant to support a conclusion:

- ensure every premise and conclusion has its own statement record;
- add one or more `corpus/inferences/*.json` records for the logical steps;
- add a `corpus/arguments/*.json` record composing those steps;
- add `Challenge.lean` containing the exact advertised theorem with `sorry`;
- add a separate `Solution.lean` containing the same theorem and a real proof;
- run `scripts/root-imports.sh --write` so `TruthCore.lean` imports every new module (except `Challenge.lean`) in sorted order;
- add a `corpus/results/*.json` verification record that points to the argument;
- add a Comparator JSON config naming the theorem and permitted axioms.

Scoped assumptions and discharged assumptions belong to inference records. They are not ordinary established corpus premises.

### 6. Handle missing premises correctly

If a Solution cannot be proved from the advertised premises:

- do not add an axiom;
- do not strengthen a definition;
- do not broaden an existing source claim;
- create a candidate describing the missing philosophical proposition and the source location that should be investigated.

### 7. Verify the three boundaries

Run:

```bash
python3 scripts/source_evidence.py check
python3 scripts/source_evidence.py verify
lake build
python3 scripts/corpus.py check
python3 scripts/corpus.py bind-check
scripts/verify-result.sh <RESULT-ID>
```

`corpus.py bind-check` (after `lake build`) reads each result theorem's type and checks that its `Prop` hypotheses are exactly the argument's premise statements and its result type is the conclusion statement, matched by `lean_declaration` head constant; type and vocabulary parameters are not premises. A hypothesis whose head is a theory definition (`TruthCore.Comparison.*`) is a theory bundle: it is unfolded one step and split on `∧`, and each conjunct must bind to a listed premise, covering them exactly. A conclusion that is a theory definition is a consistency claim: its argument must list `commitment_statement_ids` (and may then have no premises), and these must match the conclusion's conjuncts in the same way. Keep non-theory conclusion propositions outside `TruthCore.Comparison`. `source_evidence.py check` verifies offline manifest and claim bindings. `source_evidence.py verify` fetches the exact pinned editions and rejects byte drift by Git blob SHA. Source fidelity remains a research/review judgment. Lean/Comparator verifies only the formal consequence.

Do not call an argument mechanically verified unless its result passes Comparator. CI also runs an independent no-`sorry` NanoDa check over the built library.

### 8. Self-sweep before requesting review

Before requesting `@codex review`, apply the Review guidelines below to your own diff in one pass and fix what you find:

- every "read as" or attributed claim states no more than its cited sentence; any strengthening is stated as an explicit, unattributed open premise;
- every load-bearing term on a root path links a definition through `definition_ids`;
- every ambiguous term links a disambiguation through `disambiguation_ids`.

## Review guidelines

Every code review (including `@codex review`) has one more job besides finding bugs: the reviewer must try to **understand and accept** each proof the change presents. The repository, not the reviewer's background knowledge, has to make the proof convincing. Apply this to every result, argument or statement that the change adds or modifies and that lies on a path to a root (`python3 scripts/corpus.py frontier --reaching-root` lists the root paths; `STMT-CATHOLICISM-TRUE` is the default root). For each one:

1. **Restate it.** In a few sentences, say what the argument concludes, from which premises, through which steps, and which Lean theorem binds it (`corpus/results/*.json` → `theorem`; the Challenge module freezes its type). Then say whether you accept that the conclusion follows, on the evidence in the repository: the Lean statement, the premise statements and their claims, and the definitions below. Lean checks consequence; you check that the Lean statement says what the prose and the source claim say.
2. **Find the definition of every load-bearing term.** List each term whose meaning the conclusion depends on (for example *being*, *act*, *potency*, *cause*, *per se*, *maxime ens*, *God*, *true*). Locate its definition: a `corpus/definitions/*.json` record (`DEF-…`) linked from the statement, claim or argument through `definition_ids`. A definition is either sourced (its `claim_ids` point to the claims whose pinned passages give it) or stipulative (its `note` says why, and what would source it). Check that the definition matches the Lean declaration it names and the way the statement uses the term.
3. **Find the disambiguation of every ambiguity.** Where a term has more than one sense, a reading choice is made, or two premises could use a word differently, locate the `corpus/disambiguations/*.json` record (`DISAMB-…`), linked through `disambiguation_ids` or reached because a linked definition is one of its `sense_definition_ids`. Check that its `resolution` says which sense each use takes and why the argument does not pass from one sense to another.
4. **Report gaps by severity.** Each finding must say exactly what is missing (the term, the statement or argument ID, and what a definition or disambiguation would have to say). Each of the following is a P1 finding:
   - a load-bearing term with no definition record at all, or with a definition that is wrong in a way that changes what is proved (it does not match the Lean declaration or the statement's use);
   - an ambiguity, equivocation risk or reading choice with no disambiguation, or whose disambiguation does not cover this use;
   - a reading step that is not stated: the prose or claim says more or less than the Lean statement, and no record says which reading is formalized;
   - a gap between the Lean statement and its prose paraphrase or its source claim (quantifier scope, modality, time, identity, causation, or a parameter the prose treats as defined);
   - any proof, prose or record that claims more than its source or its Lean theorem supports.

   A missing `definition_ids` link is P2, not P1, when the term already has a correct definition record, or when the gap is covered by the definition-coverage issue #216. Report all such missing links in one finding per review, not one per cycle.

   If you would write "this depends on what is meant by …", the repository is missing a definition or a disambiguation: report that as P1 instead of guessing the intended sense. Do not report as P1 that a premise is open or that you doubt its truth; open premises are the frontier and are allowed. Report only what stops you from understanding and accepting the step as presented.

5. **Report everything in one pass.** Report every finding you can identify in a single review, grouped by kind (overstated or unstated readings, missing definitions, missing disambiguations, Lean/prose gaps, other bugs). Do not stop at the first finding. Before finishing, re-check every attributed claim and every `definition_ids` and `disambiguation_ids` link in the diff. Handling is unchanged: P1s that overstate a proof are fixed in the PR; P2s and coverage gaps go to #216 or a follow-up issue.

`python3 scripts/corpus.py check` enforces the mechanical part: every `definition_ids` and `disambiguation_ids` entry must resolve, a sourced definition needs known claims, a stipulative one needs a note, a disambiguation needs at least two known senses, every definition must be used, an argument whose conclusion, premises or commitments use two senses of one disambiguated term must link that disambiguation, and every `STMT-`, `DEF-` or `DISAMB-` id cited in their prose must exist. It cannot tell whether a term *should* have been linked; that judgment is this review's job. The explorer shows the terms on each statement, claim and result page and lists them all at `/definitions`.

## Naming

Lean namespaces follow the source hierarchy, e.g.:

```text
TruthCore.Greek.Plato.Timaeus
TruthCore.Greek.Aristotle.Physics
```

Claim IDs are stable provenance/interpretation IDs:

```text
PLATO-TIM-28A-CAUSE-A
PLATO-TIM-28A-CAUSE-B
```

Statement IDs are stable proposition IDs and should not encode an assertion that two source readings are identical:

```text
STMT-CAUSE-PRINCIPLE-BROAD
STMT-COSMOS-HAS-CAUSE
```

Passage IDs identify reproducible source evidence ranges, not interpretations:

```text
PLATO-TIM-28
ARIST-PHYS-I-4
```

Argument IDs identify a composed derivation. Result IDs identify a verifier record and may intentionally match the argument ID in the seed corpus:

```text
PLATO-TIM-28A-28C-COSMOS-CAUSE-A
```

Do not renumber existing IDs merely because new earlier material is added.

<!-- BEGIN:turborepo-agent-rules -->

# This is NOT the Turborepo you know

Turborepo configuration, task behavior, and CLI commands can vary between installed versions and may differ from your training data. Resolve the `turbo` package from this file's directory or relevant workspace; in monorepos, it may not be visible from the repository root. For example, run `node -p "require.resolve('turbo/package.json')"` from a workspace that depends on `turbo`.

Read `docs/README.md` inside that installed package first, then read the relevant pages from its `docs/` directory before changing Turborepo configuration or commands. Heed deprecation notices. These bundled docs match the installed package version and are available without network access.

This block is written and re-added by `turbo` before repository-scoped commands when an AI agent is detected. In the Turborepo source repository, its template is defined in `crates/turborepo-cli/src/cli/agent_guidance.rs`. Removing the managed block while updates are enabled means a later qualifying invocation will add it again. Set `"agentGuidance": false` in the root `turbo.json` or `turbo.jsonc` to opt out; this does not remove an existing block. Keep the block committed with your work to avoid an uncommitted change on the next agent invocation.
<!-- END:turborepo-agent-rules -->
