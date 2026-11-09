# Codex worker contract

This repository advances substantial arguments through small verified research steps. Keep the complexity in the philosophy, not in repository machinery.

## Fresh subagents for issue work (owner direction, 2026-11-08)

During a workloop, the coordinator delegates each issue or bounded investigation
to a fresh subagent. Split broad issues into independently reviewable slices;
give each worker one slice with explicit file and argument ownership. The
coordinator owns coverage, priorities, shared instructions, integration and merges.

- Start workers without inherited conversation history (`fork_turns="none"`,
  or the equivalent). Supply the brief below, relevant repository instructions,
  exact corpus/theorem references, and the current workspace/service setup.
  Do not forward the coordinator's transcript as the brief.
- Use isolated warm checkouts for writers, with distinct ownership. Serialize
  shared heavy verification and Lean-service operations under the existing
  protocol. Workers must accommodate others' changes, not revert them.
- Reuse a worker only within its current bounded slice. Start a fresh worker
  for the next issue or unrelated argument family; workers do not recursively
  delegate unless their brief explicitly authorizes it.
- Workers persist substantive findings in the existing corpus records or linked
  notes, then return a compact delta: PR/head, verified and unverified scope,
  findings and remaining gaps, with evidence links. The coordinator updates the
  one current handoff rather than importing long worker transcripts or creating
  another tracker. Reuse unchanged verification evidence.

## Worker brief and handoff

The master gives each worker a four-line brief:

1. **Target:** the skeleton node, argument or root obligation advanced. It must be a node on a root route, or connect to one by a named bridge. A target that serves no root route is rejected (see "Connect every library to the case").
2. **Reuse:** the existing statement IDs and exact Lean theorems to consume.
3. **Missing step:** the inference or source reading still needed.
4. **Premise comparison:** the expected premises retained, added or removed, and whether the work connects results or discharges an obligation.

For a substantial frontier investigation (not a single source reading), the brief or the existing investigation issue also carries a compact **investigation brief**: the thesis and its downstream purpose; the strongest case and the strongest rivals; the existing results reused; the decisive missing bridge or fork; and the expected premise or configuration delta. It lives in the one current handoff or issue, not in another tracker.

The PR reports the actual premise comparison by linking or pasting the computed delta (`python3 scripts/corpus.py frontier-diff --base <merge-base>`; CI prints it to the job summary of the "Report the premise frontier" step), not a hand-reconstructed list; a new connection is not itself a discharge. A new verified, non-transcription argument is positive **conditional support-option** progress even if it replaces one leaf with several open premises in the expanded-route diagnostic. Record those new obligations separately; neither the new argument nor a lower route cost establishes its conclusion. For non-proof work, use “none” or “no premise change” where applicable.

The coordinator runs `python3 scripts/worker_env.py --check` once for the
selected toolchain/cache setup and supplies that setup to workers. Workers use
`python3 scripts/worker_env.py -- <command> <args...>` without repeating the
preflight unless the setup changes. Keep machine-specific verifier paths in
repository-local Git configuration or the explicit environment, not in briefs
that workers must reconstruct or in committed source.

Workers reuse a warm clone rather than compiling TruthCore cold: retain a
quiescent prepared clone, or prepare a new one with
`scripts/prepare-worker.py --seed-build-from <WARM-CLONE>` under the heavy-job
lock ([worker startup](docs/worker-startup.md)). Lake then rebuilds only modules
whose inputs changed. A seeded build output is readiness, not verification:
build, binding, axiom, Comparator and NanoDa gates still run on the final inputs.

Before handoff or retirement, persist verified source findings, rejected interpretations with reasons, and remaining gaps in the existing passage, claim, definition, disambiguation or candidate records, or their linked repository notes. Keep precise witness locators and distinguish sourced readings from open commitments; temporary files must not be the only copy. Do not create claims merely to record research activity.

## Concise reporting and persistence

1. **Report changes.** Progress updates state a new finding, decision, failure,
   merge or blocker. Do not repeat unchanged plans, status summaries or check
   inventories. During a long wait, use one short verified-wait update.
2. **Report timings only when relevant.** Include durations and resource metrics
   for requested performance work or an unexpectedly slow run. Omit routine
   startup/build histories and unavailable-metric disclaimers; ordinary timing
   evidence stays in the existing CI or command logs.
3. **Keep PRs focused.** Explain the problem, change, premise effects, essential
   validation and remaining gaps. Preserve the required claim/type self-sweep
   and exact premise comparison; take the latter from the computed
   `corpus.py frontier-diff` delta in the CI job summary rather than
   reconstructing it by hand. Link existing check evidence instead of
   narrating the execution chronology or repeating successful-check inventories;
   include a reproduction command when the linked evidence is insufficient.
4. **Maintain one current handoff.** The coordinator updates the designated
   handoff note or issue rather than creating parallel progress documents.
   Include the exact head/branch, open work, verified and unverified scope, and
   next concrete step. Workers return their task delta and references; the
   handoff links those findings rather than copying them.
5. **Preserve research substance.** Keep sources and precise locators,
   interpretations, rejected approaches and reasons, counterexamples, proof
   boundaries and remaining gaps in their existing corpus records or linked
   notes. Shorter reporting must not remove this evidence. Do not replace it
   with chat history, temporary logs or duplicated progress narratives.
6. **Trust completed work; do not repeat verification.** Reuse worker reports
   and successful check evidence when the checked inputs and relevant
   dependencies are unchanged (owner instruction, 2026-10-28). Use focused
   diagnostics during development and final CI for the delivered revision;
   do not independently repeat full builds, binding, Comparator, NanoDa, test
   suites or review rounds at every handoff. Rerun affected checks for relevant
   changes, concrete failures or unresolved findings. Complete the claim/type
   self-sweep for a related batch before its first push, and combine related
   findings into one reviewable PR where practical.

## Local server experiment for the next workloop

At the start of the next workloop, the master should run a bounded experiment
with workers interacting with a local service. Inspect the available tooling
first: the explorer development server alone does not expose Lean verification.
If an agent-facing service exists, start it and check its health. Otherwise,
assign one bounded lane C task to implement the smallest usable adapter around
the existing corpus/configuration commands and Lean language server; do not
assume an endpoint or startup command already exists. Document the actual
startup, health-check and client commands before asking workers to use it.

The master owns service startup and shutdown and gives participating workers
the endpoint, supported operations and workspace/session identity alongside
their normal brief. Have workers try corpus queries and repeated Lean proof
edits through the service, using persistent Lean sessions for diagnostics and
proof goals. Keep agent workspaces and Lean sessions isolated; queue expensive
verification jobs and bind every response to its exact revision and inputs.
Reuse existing CLI and corpus semantics rather than introducing a second
proof-status registry. Keep the service local to the machine.

Compare a small representative task with the CLI workflow, recording useful
latency/setup differences, correctness issues and a retain/revise/remove
recommendation in the existing handoff. Continue via the CLI if the experiment
fails; it must not block research. Interactive diagnostics do not replace the
required build, binding, axiom, Comparator and NanoDa checks on the final inputs.
Reuse the pinned Lean toolchain and existing dependencies; this experiment does
not authorize adding an external Lean dependency.

## Premise dossiers and attempts

Before opening a new proposition investigation or introducing vocabulary, run
`python3 scripts/corpus.py related <STMT-ID>` for the load-bearing seed. It reuses
or refreshes a disposable local index and surfaces related propositions, complete
argument bundles and previous attempts. Inspect promising matches before
reinventing them. Rankings and shared vocabulary are discovery aids, not proofs
of equivalence, implication or incompatibility. Continue with the dossier and
existing certification workflow below. The repository-local `proposition-reuse`
skill in `.agents/skills/proposition-reuse/SKILL.md` describes this entry point.

When the target is an existing argument or result, start with
`python3 scripts/corpus.py context <ARGUMENT-OR-RESULT-ID>`: one bounded pack with
the frozen Lean statement, Lean-import reuse, premise status and other routes,
countermodels, attempts and open work, derived on demand (`docs/notes/argument-context.md`).

For every premise touched, inspect `python3 scripts/corpus.py dossier <STMT-ID>`
(the explorer links the same generated dossier from the statement page). Before
handoff, update `corpus/attempts/` for failed derivations, rejected readings,
source searches, and other substantive attempts, including successful results.
Reuse an existing attempt when correcting its record; do not create a philosophical
claim merely to log activity. Record exact target statement IDs, outcome, concise
findings, remaining blocker when blocked, and result/claim/PR evidence. A successful
attempt does not establish its target or change frontier closure. The dossier is
computed from corpus records, not edited separately. See `docs/premise-dossiers.md`
for the attempt format and reference boundaries.

## Research hypotheses are not forced owner decisions (owner direction, 2026-11-09)

- Before offering A/B/C as an owner choice, classify whether the alternatives are mutually exclusive *actions or bindings needed now*, or coexisting philosophical senses, explanatory standards, rivals or conditional frameworks. A disputed thesis is not itself an implementation decision gate.
- For research alternatives, retain each defensible interpretation and its strongest arguments, objections and replies. Compare precise implications, countermodels and bridges under explicit assumptions; investigate relationships before assuming either exhaustiveness or exclusivity. Do not ask the owner to select a metaphysical winner merely to proceed. A recommendation can prioritize investigation but does not establish a sense.
- Ask a focused owner question only when a concrete next action actually requires an exclusive commitment that cannot responsibly be carried as explicit alternatives. An instruction to investigate all options is a complete methodological decision: persist it and proceed without reopening a forced winner question.
- Whole-series explanation example (PR #1297): retain (A) optimality with possible ties, (B) genuine nonnecessitating agent-causal exercise, and (C) strong contrastive sufficiency as rival standards to test, not an asserted exhaustive/exclusive trilemma. The existing first-optimum agenda is one procedural selector, not proof of agent causation; a `chooses` predicate alone is not explanatory authority. B is a provisional investigative preference, not an established conclusion. Include choices, laws and relations in the full contingent order; inspect reason relevance, circularity, regress, contingency and the missing source-to-adequacy bridge. None of this closes the original premise.

## Systematic sense and rival comparison

Before research, inspect `/progress` in the corpus explorer and the target's
`/dossiers/<statement-uuid>#research-comparison`; use
`python3 scripts/corpus.py context <ARGUMENT-OR-RESULT-ID>`,
`python3 scripts/corpus.py dossier <STMT-ID>` for every touched premise, and
`python3 scripts/corpus.py related <STMT-ID>` before introducing vocabulary.
These views reuse canonical corpus evidence; they are not a separate status registry.

- Pick a bounded root-route target and a named rival/sense question. Use a finite,
  explicitly scoped set of relevant senses. State coverage and exclusivity as
  explicit assumptions; absent mappings remain unknown or untested.
- Compare within the same meaning, witness, domain and frame. Each cell records
  a checked exclusion under listed premises, model-witnessed compatibility of
  the selected bundle, an unresolved exact gap, or untested. An absent refutation
  is not compatibility; a finite countermodel is not global incompatibility.
- Keep every assumption visible. A newly verified non-transcription argument is
  positive conditional support-option progress even with more explicit open
  inputs; it establishes its conclusion only under the existing closure rules.
  No independent defense of primitives is required merely to explore consequence.
- Before handoff persist evidence, exact gaps and the next concrete research step
  in existing corpus records, batch specs and `corpus/attempts/`, not another
  research/status registry. Attempts do not confer proof status. Use existing
  explicit configuration semantics and certificates for assumption comparisons;
  registration alone remains `verification required`. Generate batch records with
  `python3 scripts/argument_batch.py records SPEC --write --fix` and inspect the
  resulting dossier. The static progress view derives closure/support from
  `frontier --json`, gaps from dossiers/attempts, senses from disambiguations, and
  scoped comparisons from existing configuration reports. Record explicit sense/rival certificate annotations as
  `[[argument.research_comparisons]]` in the owning batch spec (fields and commands
  in `docs/github-pages.md`, “Recording a checked sense/rival comparison”); the
  generator writes them to the existing result record. Missing mappings stay
  untested, never inferred from names or imports. These annotations do not
  bypass theorem verification or alter closure.
- The coordinator selects the next unanswered discriminating cells and assigns
  workers disjoint argument clusters. Reuse unchanged checked evidence. Report
  conditional support progress separately from establishment and root closure.

## Logic first; attribution deferred (owner direction, 2026-11-05)

The current priority is formalizing the arguments from **Carneades.org** and
exploring their logical consequences. Do not let source acquisition or author
exegesis displace this work.

- Start from available argument summaries, transcripts, existing propositions
  and explicit working reconstructions. Formalize premises and conclusions,
  compose results, find incompatible bundles, and construct countermodels.
- Treat uncertain premises and interpretations as openly stipulated framework
  inputs. Record variants when needed. Neither source attribution nor an
  independent defense of each premise is a prerequisite to studying consequence.
- **Do not put PDF downloads, transcript authentication, passage pinning,
  extraction portability, or getting an author's intentions exactly right on
  the critical path of a logic task.** Do not build source infrastructure to
  unblock such a task. Defer that work until explicitly selected by the owner.
- New formalizations do not need new source, passage or claim records. Label
  them as analyst formulations with attribution deferred; keep already available
  titles/URLs/locators as navigation, not as verified historical claims. Preserve
  completed source findings in existing notes, candidates or attempts without
  spending more effort to certify them now.
- Existing source-integrity rules still apply when deliberately publishing a
  source claim. They must not be bypassed or replaced by invented attribution.
  If a new attribution blocks a logic PR, defer the attribution and its new
  witness records while retaining the propositions and checked logical work.
- Keep Lean, binding, Comparator/NanoDa, frozen Challenges, exact premise
  reporting and countermodel boundaries. A conditional consequence does not
  establish its premises or the Catholicism root as true.
- Parallel workers should own distinct argument clusters and files, preferably
  seemingly unrelated topics. Use isolated clones and serialize shared heavy
  verification/service operations; do not manufacture overlapping source tasks.

This direction overrides source-first and source-coverage priorities elsewhere
in this file and in existing issue briefs for the current logic-first phase.
Attribution can be revisited when the source tooling is ready or the owner
explicitly requests it.

## Encode first (owner direction, 2026-11-03)

Formalize what can be formalized. Derive what can be derived. Document only what cannot yet be encoded.

- **Encodings must be able to fail.** A transcription or an opaque flag is documentation in Lean syntax, not formalization (invariant 16).
- **Interpretation forks become sibling propositions.** Where a point is open to interpretation, create one claim or statement per defensible option (invariant 5), linked by `interpretation_of` or a disambiguation, not "reading A / reading B" paragraphs in a note.
- **Strength forks become strong and weak versions (#1017).** Where the ambiguity is one of strength (for every S, or only for the sentences the argument uses), record both versions as sibling statements and register the order with a `strengthens` relation (strong → weak). It is valid only with a verified result whose argument has the strong version as its only premise and the weak version as its conclusion; a strictness countermodel is optional. Use the **weakest version that suffices** in each argument; an argument that keeps the strong version records why in `strong_version_needed`. Each version gets its own claims: a source that states only the weak version is never attributed the strong one. Senses that differ in content rather than strength (eternity and sempiternity, #979) stay a disambiguation. See `docs/corpus-model.md`, "Strength order".
- **Disambiguate through definitions, not labels.** Each consequential `TERM_1`/`TERM_2` sense needs its own `DEF-…` record and a faithful formal interpretation. Reuse and, when needed, define the load-bearing terms *inside* its definition, recursively; this may grow into an extensive shared dictionary, with no arbitrary depth limit. A Lean primitive is allowed only when explicitly identified as primitive, with its meaning, distinguishing conditions and open semantic obligations stated. A primitive relation or a theorem that merely constrains it is not a completed Lean definition. Do not conceal a contested bridge in definitional equality or create circular definitional unfoldings. See `docs/corpus-model.md`, "Definition dependencies and formal meaning".
- **Terms carry sense labels (owner direction, 2026-11-07).** Each disambiguated term has numbered senses TERM_n (PRIOR_1, PRIOR_2) with opaque uuid identities; labels are stable and only appended. Each sense is a distinct Lean type (`senses[].lean_declaration`), so equivocation is meant to be a type error that `bind-check` catches; a sense label without a distinct Lean declaration is not a finished sense. One argument uses one sense per term. An argument valid in several senses becomes one argument per sense (`for_each_sense` in `argument_batch.py`). A passage between senses is an explicit premise listed in `sense_bridges`, or the conclusion of an argument that derives it (`role: "conclusion"`); a premise-free control showing that mixing fails sets `sense_mixing_control: true`. The legacy allowlist in `corpus/sense-index-allowlist.json` may only shrink (#1233). See `docs/corpus-model.md`, "Sense-indexed terms".
- **Prose residue names its blocker.** Prose is legitimate for source-fidelity judgments, rejected interpretations with their reasons, and what cannot yet be typed. Each such residue says what encoding it would need: vocabulary, a source, or a judgment that cannot be encoded.

## Exploration and batch certification (owner direction, 2026-11-07)

Breadth matters as much as certification. For a target proposition, first write an **exploration map** (`explorations/<slug>.toml`, checked with `python3 scripts/argument_batch.py map`): the whole argument DAG in one pass, reusing existing statement IDs and marking new nodes and bridges. Then certify a cluster of derivations as **one batch**: one vocabulary module, one Solution, its Challenge generated by `python3 scripts/argument_batch.py challenge`, and all corpus records generated from one spec by `python3 scripts/argument_batch.py records SPEC --write --fix`. New bare premises and analyst bridges are kept and labelled open; adding them is not a regression (the former no-bare-premise relocation rule is discarded). Controls: one nonvacuity witness per batch and omission countermodels for the premises that carry the argument. Report exploration progress with `python3 scripts/corpus.py thickness --base <merge-base>`. Base every PR on `main` (no stacked PRs: deleting a merged base branch closes the PRs stacked on it). The coordinator merges worker PRs with `python3 scripts/merge_queue.py --workdir <spare clone> PR...`, which merges green PRs and resolves conflicts that lie only in generated aggregators by regenerating them; any other conflict goes back to the author. Before each round, use the worklist (`thickness --queue`) and record rejected leads as attempts.

## Connect every library to the case (owner direction, 2026-11-07)

**What went wrong.** The repository built a large modal library for the necessary-being target: about 50 modules under `TruthCore/Modal/`, with roughly 89 verified results on Kripke frames, K/T/S4/B/S5, actualist domains, rigid designation and modal collapse. None of those results reached `STMT-CATHOLICISM-TRUE`. The necessary-being routes kept running only through act/potency and degrees-of-being chains, and their "necessary" was never the necessity of modal logic.

`DISAMB-NECESSARY` listed ten senses of "necessary" and stated that no statement relates them. Research rounds selected their work from `thickness --queue`, which ranks only statements that already reach the root, so the disconnected library never surfaced. The rounds optimised thickness and never asked what verified work was idle. A framework that answers no question on a root route is not progress on the case, however well verified.

**The rule.** No library, framework, vocabulary or result family is built or extended in isolation.

1. **Name the target before building.** Every worker brief and every PR that adds vocabulary or results names the root-route node it serves: a premise it discharges, an argument it connects, or a rival it refutes. `python3 scripts/corpus.py frontier --routes` lists the routes.
2. **Connect, or say why not.** The PR either shows the connection in the computed `frontier-diff` (new results reaching the root, a premise closed or defended, a route re-routed) or states an explicit connection plan: the target statement, the missing bridge and its blocker. The coordinator's handoff tracks that plan. Unconnected work does not count as progress on the case until it is connected.
3. **Audit idle work before each round.** Before selecting a research round, list the verified result families that do not reach the root (`truth orphans`, once merged). Connect large disconnected families before opening new derivations. Judge rounds first by route cost and defended premises (`frontier-diff`); thickness is secondary.
4. **Fork load-bearing terms; do not keep senses in silos.** When a term on a root path has several senses (a disambiguation listing them), proceed in this order:
   - (a) Add two explicit open premises. COVERAGE: "senses A, B, … are all the relevant senses". EXCLUSIVITY: "exactly one sense applies to this use". Formalize exclusivity as the intended reading selecting one constructor, or as mutually exclusive cells, because senses may be strength-ordered and need not have disjoint extensions.
   - (b) Ground each sense in its own definition record and Lean interpretation. Follow consequential terms in those definitions to further definitions/disambiguations. If a relation is primitive, distinguish it from a definition with a body and record the open semantic constraints; do not treat a premise about it as its definition.
   - (c) Make a typed enum of the senses, each referring to its sense-specific Lean declaration; names and distinct types alone do not establish the intended meanings.
   - (d) For each sense, prove the route step, or show it fails with a countermodel or a `refutes` relation. Test proposed equivalence, implication and independence between senses rather than assuming any of them.
   - (e) Prove a joint theorem by cases, with coverage as a premise. Record `strengthens` between senses where one implies another.

   Only then attack rival semantic commitments and worldviews: the fork turns their refutation into a checked disjunctive syllogism instead of ad hoc rebuttals. A disambiguation whose resolution says its senses are unrelated marks an unfinished fork, not a finished analysis.

See `docs/decisions/2026-11-07-02-connect-libraries-to-the-case.md`.

## Proof-seeking stance

- Seek machine-checkable consequence, not prose approval. An LLM may propose readings, propositions, formalizations, or proof steps, but its agreement is never evidence that a conclusion follows.
- Use Curry–Howard as the default mental model for formal work: propositions correspond to types and proofs to terms/programs; implication is a function type, conjunction a product, disjunction a sum, and quantified propositions may require dependent function or pair types.
- When claiming `P1, ..., Pn ⊢ C`, make the premises, definitions, and inference rules explicit and reduce the claim to a mechanically checkable artifact, using Lean by default in this repository.
- Keep source interpretation, proposition extraction, formalization, proof search, and proof verification distinct. Lean's kernel verifies accepted proof terms; tactics, solvers, and LLMs are search helpers, not authorities.
- Machine-checkable does not mean automatically discoverable. Failure to find a proof is not a refutation, and formal verification establishes consequence only inside the encoded system—not premise truth, source fidelity, empirical truth, or completeness of the chosen logic.

## Conditional framework exploration (owner direction, 2026-10-31)

Truth Core retains its purpose: investigate the case for Catholicism and the strongest competing worldviews. In the foundational phase, systematically explore combinations of low-level propositions, rules, framework commitments and semantic profiles, including routes to necessary concrete being and alternative conclusions. Do not turn this into an endless demand to justify each primitive assumption before studying its consequences.

- **Assumptions are legitimate research inputs.** A framework may take agency, causal structure, a PSR variant, a modal rule or another contested commitment as given. Declare the commitment and its interpretation explicitly; distinguish stipulated framework assumptions from claims attributed to sources. Independent proof of the assumption is not a prerequisite for conditional investigation.
- **Explore the configuration space.** Compose checked results, seek multiple routes to the same conclusion, minimize sufficient assumption bundles, derive incompatible cores, and construct joint models of surviving branches. Compare changes when consequential commitments are added, removed or reversed. Keep the logic and semantic profile fixed for each comparison, or mark the required bridge.
- **Classify outcomes precisely.** Record conditional entailment, contradiction under stated assumptions, a model-witnessed alternative, or unresolved search. A failed proof search is not a refutation; an inconsistent background cannot support a nonvacuous victory. An abstract model witnesses only the stated formal interpretation.
- **Count conditional progress.** A new implication, weaker sufficient premise set, incompatibility, countermodel or distinguished alternative is genuine research progress even when no philosophical premise is independently defended. Report configuration/derivation progress separately from the existing root-frontier closure status; do not silently claim that a conditional theorem establishes a premise or the root as true.
- **Avoid recursive premise-defense by default.** Investigate independent warrant, source interpretation or real-world applicability when that is the selected research question, when it discriminates serious surviving alternatives, or when an unconditional truth claim is being made. Otherwise keep the assumption open and continue exploring configurations. Do not automatically spawn a new source task for every open primitive.

Existing Challenge/Solution boundaries, source fidelity, exact premise reporting, no-smuggling rules, and root-closure criteria remain in force. This direction governs research priorities and the interpretation of progress; it does not declare any particular framework's assumptions true.

## Semantic grounding of metaphysical relations

Every newly introduced or substantially reinterpreted relation involving causation, dependence, grounding, contingency, necessity, or explanation must have a clear, non-equivocal interpretation. Its independent applicability to reality may remain open while the relation is explored as an explicit framework assumption.

For philosophically significant relations:

1. Explain their meaning in ordinary language.
2. Identify concrete examples and counterexamples, or explicitly record why examples remain unavailable.
3. Distinguish them from superficially similar relations.
4. State structural properties such as transitivity, asymmetry, and well-foundedness explicitly; when their real-world applicability is claimed, defend that interpretation or mark it open.
5. Mark any generalization from ordinary experience to metaphysical claims as an explicit bridge; investigate both accepting and rejecting it when consequential.
6. Test the interpretation against serious competing accounts.

A formally verified theorem establishes a conditional consequence, not the truth or applicability of its metaphysical interpretation. This is a boundary on what may be claimed, not a prerequisite to independently prove each premise before exploring the framework. Never treat a mathematical relation as genuinely causal or explanatory merely because of its name.

## Permanent invariants

1. **Research before formalization.** Every source-derived claim must point to a stable source record and a precise locator. For a copyrighted work with no pinnable witness, that locator may be a `bibliographic_span`: edition, ISBN or DOI, and exact pages or section, without pinned bytes (owner decision 1c on #378; see `docs/source-evidence.md`).
2. **Materialize, do not remember.** Before formalizing a source-derived claim, resolve or create its `corpus/passages/` witness and run `python3 scripts/source_evidence.py materialize <PASSAGE-ID>`. Read that verified text and enough context to interpret it. Model memory, a search snippet, or a plausible citation is never source evidence. A `bibliographic_span` has no bytes to materialize (`materialize` refuses it): claim from it only after reading the cited pages in the edition itself, never from memory, and its claims carry `witness: "bibliographic"`, so they are shown as not byte-verified.
3. **Source integrity is not source fidelity.** A pinned revision, Git blob hash, CTS path, and successful materialization establish which source text was consulted. They do not establish that an interpretation is correct. Preserve that scholarly judgment separately.
4. **Statements have independent identity.** A statement is a proposition used by logic. A claim says that a source supports a statement under an interpretation. Never make statement identity depend on source provenance.
5. **One defensible reading per claim.** If two materially different interpretations are both reasonable, create two claims. They may point to distinct statements even when later work could relate those statements.
6. **Do not merge by similarity.** Textual identity, translation equivalence, formal equality, logical equivalence, philosophical equivalence, and historical identity are different possible relations. Add relations later; do not silently merge statement IDs.
7. **Reuse before invention.** Search existing statements and Lean declarations before adding vocabulary. Reuse only when the meanings genuinely coincide; a false identification is worse than a duplicate statement.
8. **Weakest faithful formalization.** Do not strengthen a source passage to make later arguments easier.
9. **No premise smuggling.** A proof worker may not silently add an axiom, assumption, definition, or stronger reading to an existing argument or frozen Challenge solely because its proof needs it. Register a consequential stronger assumption as a separate, explicitly labeled framework configuration or candidate and compare its consequences. Source it when attributing it to a text; an openly stipulated framework commitment need not be independently proved to be explored. It does not close a root premise.
10. **Inference is explicit.** Arguments connect statement IDs through inference-application records. Never encode a logical step as an overloaded bare statement-to-statement edge.
11. **Global cycles are allowed; circular proof is not.** Semantic relations and mutually supporting statements may form cycles. Each advertised argument must still be grounded in its premises and mechanically checked by Lean/Comparator.
12. **Challenge is frozen before solution work.** Never weaken or otherwise edit a Challenge merely to make the Solution pass. If source review changes the statement, treat that as a new/revised claim first.
13. **Formal verification is not source verification.** A result verifies an argument's formal consequence. It does not establish that a source really meant a statement or that a premise is philosophically true.
14. **Mathlib for mathematics; no other dependency without an owner decision.** Mathlib is an approved dependency for mathematical content: analysis, order, set theory, ordinals and cardinals, combinatorics. Prefer an existing Mathlib notion over a hand-rolled one. Do not use Mathlib to dress up opaque propositions: importing it adds no philosophical content. A result whose proof uses Mathlib may permit exactly `propext`, `Classical.choice` and `Quot.sound`; a result that does not import Mathlib stays zero-axiom (`docs/axiom-policy.md`). `lean-toolchain` pins the exact Lean version the pinned Mathlib release requires. Any other external Lean dependency still needs an owner decision (#337).
15. **Do not build identity infrastructure early.** No graph database, RDF ontology, embedding-based merger, or canonical-equivalence resolver until the corpus creates a concrete need. The typed JSON records are sufficient for now.
16. **A transcription is not a proof.** A result whose proof only applies a premise whose consequent already is the advertised conclusion (`exact hBridge ⟨…⟩`), or whose atoms are opaque `Prop`s that nothing constrains, certifies only that "therefore" was transcribed. Such a result may still be recorded as a faithful map of a source argument, but the PR and the result record's description must call it a transcription. It does not count as progress on the case and closes no frontier node by itself (see `docs/systematic-corpus-loop.md`). The one exception is closure carried through it: a transcription closes its conclusion exactly when **every** premise of its argument is already closed—self-evident, alternatives all refuted, the conclusion of a non-transcription result, or itself closed by this same rule (computed as a fixpoint; owner decision on #143, 2026-10-24). A transcription with any open premise, such as an open `A ∧ B → C` bridge, leaves its conclusion open. Where the philosophy has internal structure, formalize that structure with typed vocabulary (beings, respects, causes, sentences, …) so the conclusion is *derived* and the result could have failed. Likewise, a hand-rolled substitute for a notion Mathlib already provides (for example "eventually constant" in place of convergence, or a bespoke ω+1 in place of an ordinal or order embedding) needs a stated reason in its doc comment.
17. **Compose, do not restate.** Build on earlier results by importing their Lean modules and using their theorems. Do not restate a proved conclusion as a fresh premise. Reuse shared typed vocabulary where meanings coincide (invariant 7); a new per-file `…Reading` vocabulary for a concept the corpus already has needs a stated reason.
18. **Source kinds are frozen.** After `media_span` (#152), `web_snapshot` (#154) and `bibliographic_span` (#378), add no new source kind without an owner decision. A `bibliographic_span` is the last resort: allowed only for a copyrighted work when no pinnable witness (git text, public-domain edition, `web_snapshot` of a legitimately hosted copy) exists, with a `why_bibliographic` note; upgrade it to a pinned witness when one becomes available. When not even a bibliographic citation can be read and given, keep the claim as a candidate marked as waiting for a witness, and continue the reasoning with its statement as an explicit open premise. Sourcing must not block reasoning, and reasoning must not fake sourcing.
19. **truth-core is self-sufficient.** Do not add runtime or CI dependencies on other repositories (historical-source-atlas, worldview-lab, solver services, …). Use one only for a concrete node that is blocked without it, and pin it like a source.

See `docs/corpus-model.md` and `docs/source-evidence.md` for the entity and verification boundaries. For the campaign to formalize the case for Catholicism (epic #143), including the owner's binding principles and the working method, read `docs/catholic-case.md` first.

## Configuration elimination and composition

For a group of related open propositions, follow [the configuration elimination loop](docs/configuration-elimination-loop.md): reuse certified results and finite models, seek minimal verified contradictory premise sets, compose proven implications, persist attempts and countermodels, and compare exact root-frontier premises before/after. Configuration labels are relative to their explicit formal semantics; absence of a model or proof is unresolved, not an impossibility claim. This supplements the source campaign loop below and does not change the frontier closure rules (#477).

Find omission countermodels with `python3 scripts/countermodel.py THEOREM [--omit HYP] [--all] [--size K]` instead of writing them by hand. It proposes finite models and has Lean check a `decide` certificate; "unresolved" is not proof that a premise is needed ([countermodels](docs/countermodels.md)).

## Argument-first investigation

Frontier-led work is **constraint discovery and elimination within an end-to-end case**. Start from related existing commitments under one explicit semantic profile. Compose checked implications, seek incompatible bundles and substantive exhaustive forks, and witness surviving branches before opening another premise investigation. Recursive premise defense is a targeted fallback when it can discriminate surviving branches, not the default engine. Keep the strongest rivals and the original question visible; recompose every finding into that case.

Follow the [certified fork workflow](docs/configuration-elimination-loop.md#certified-forks-as-the-default-frontier-workflow). A dilemma/trilemma needs a checked coverage theorem under explicit background assumptions; exclusivity is a separate obligation. A contradictory bundle forces rejection of at least one member, not a preferred member. Prefer small general constraints that prune families over issue/proposition counts. Preserve the existing proof, source, dossier and frontier authorities; conditional elimination does not establish its background or close a root premise. Split records only for consequential inference, rival discrimination, independent defense, reuse, or existing source/proof invariants.

## Outer systematic loop

Frontier slices and their open premises take priority over unrelated source coverage. Select work from the owner-scoped investigation and its current handoff/issue, not merely the oldest eligible issue or the next source candidate. If no specific slice is named, choose a related cluster on the current #143 root route where existing commitments can yield a substantive fork, implication or incompatible core. Finish or repair in-flight work and respect real dependencies.

For source ingestion when a frontier obligation needs it:

1. Run `python3 scripts/corpus.py next` for the highest-priority source candidate; each candidate is a coherent chapter/range, not a sentence or proposition.
2. Materialize its pinned witness, read the whole range and context, then process substantive readings in order under the atomic contract below. Reuse statements; preserve distinct defensible interpretations.
3. Stop at one argument cluster or a reviewable batch of roughly 5–10 source claims. Advance the same candidate's locator if unfinished; delete it only after the range is exhausted.
4. Seed the prescribed successor campaign/range before closing the current one. Continue without reprompting unless evidence is unavailable, a genuine owner scope/modeling decision is needed, a cross-cutting defect blocks verification, or the successor is ambiguous.

Keep the issue/handoff focused on the end-to-end argument; persist source and failed-attempt evidence in existing corpus records. The [systematic loop](docs/systematic-corpus-loop.md) gives brief campaign, frontier and handoff rules.

## Lanes and shared files

Work runs in parallel lanes (#416). Each lane owns directories and the corpus records about them:

- **Lane A — Fourth Way and attributes:** `TruthCore/Latin/`, `TruthCore/Case/` (stages 1–2), `TruthCore/Results/Aquinas/`, `TruthCore/Results/Case/` (stages 1–2), and their corpus records.
- **Lane B — stage 3:** `TruthCore/History/`, `TruthCore/Greek/NewTestament/`, `TruthCore/Case/Catholicism/StageThree/`, `TruthCore/Results/Case/Catholicism/StageThree/`, `TruthCore/Results/Comparison/Resurrection/`, the module `TruthCore/Comparison/Resurrection.lean` (in lane C's `Comparison` area, so a new sibling module there is a cross-lane edit), New Testament and Church sources, and their corpus records.
- **Lane C — everything else, and the single writer of tooling:** CI, `AGENTS.md`, `scripts/`, the explorer, and all other `TruthCore/` areas.

Rules:

- Edit outside your lane only where the work needs it (for example a shared definition or disambiguation such as `DISAMB-MOTION`), keep that edit minimal, and list every cross-lane file in the PR description.
- Merge `origin/main` into your branch right before every push, then rerun the generators below and only checks whose evidence the merge invalidates. Reuse evidence for unchanged inputs; final CI covers the delivered revision.
- Shared tables and import lists are generated, never hand-edited. Lean imports: `scripts/root-imports.sh --write` (each area has its own aggregator under `TruthCore/Imports/`; `scripts/root_imports.py` lists the areas finer than one top-level directory). Docs tables and lists: add one entry file (for example `docs/decisions/<date>-<NN>-<slug>.md`) and run `python3 scripts/docs_index.py --write`. CI rejects stale output of both. After a merge conflict in a generated file, take either side and rerun the generator. A row or list item that a branch from before #416 added by hand must first move into an entry file: the generator keeps only entries.

See `docs/systematic-corpus-loop.md`, "Parallel lanes".

## One atomic work item

For each philosophically substantive reading or argument encountered inside the current candidate range, perform this loop:

### 1. Research from verified source evidence

- Resolve the passage to a `corpus/passages/` record. Its source snapshot must name the exact edition URN, repository, immutable revision, file path, Git blob SHA, source URL, language, and license. Where no such witness exists, a `web_snapshot` pins a web page by hash instead; claims on a translation carry `basis: translation`. Only for a copyrighted work with neither, a `bibliographic_span` cites the edition by page, and its claims carry `witness: "bibliographic"` (see `docs/source-evidence.md`).
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
- add `Challenge.lean` containing the exact advertised theorem with `sorry`; it stays an ordinary (non-module) file;
- add a separate `Solution.lean` containing the same theorem and a real proof;
- write the new `Solution.lean` and every new vocabulary file as a Lean module: a `module` first line, `public import` for each import and `@[expose] public section` after the imports and module docstring (`python3 scripts/convert_to_module.py convert <FILE>` converts an ordinary draft). Every library file is a module, so this always applies; CI (`python3 scripts/convert_to_module.py check`) rejects an ordinary library file other than a Challenge or an aggregator (owner decision on #986);
- run `scripts/root-imports.sh --write` so the generated aggregator of the module's area (`TruthCore/Imports/<Area>.lean`) imports every new module (except `Challenge.lean`) in sorted order; `TruthCore.lean` imports only the aggregators and changes only when an area appears. Aggregators and the root are generated as Lean modules (`public import`) while every file they import is a module (#986); never hand-edit them;
- add a `corpus/results/*.json` verification record that points to the argument;
- add a Comparator JSON config naming the theorem and permitted axioms.

Scoped assumptions and discharged assumptions belong to inference records. They are not ordinary established corpus premises.

### 6. Handle missing premises correctly

If a Solution cannot be proved from the advertised premises:

- do not change the frozen Challenge, silently add an axiom, strengthen a definition, or broaden an existing source claim;
- test for a countermodel or a useful alternative configuration and record the unresolved inference;
- when a stronger commitment is worth exploring, register a separate candidate/configuration with that assumption explicit and compare its consequences; source research is required for attributed claims, not for every stipulated framework branch.

### 7. Verify the three boundaries

The following commands describe required verification coverage, not duplicate
local runs for every worker and coordinator. Reuse completed evidence; final CI
provides the integration checks. Run a check locally when development needs it
or a relevant change or failure invalidates its earlier evidence:

```bash
python3 scripts/source_evidence.py check
python3 scripts/source_evidence.py verify
lake build
python3 scripts/corpus.py check
python3 scripts/bundle_audit.py
python3 scripts/corpus.py bind-check
scripts/verify-result.sh <RESULT-ID>
```

`bundle_audit.py` runs offline. Run it whenever you edit an argument bundle or a definition its audit pins by hash: CI runs it right after `corpus.py check`.

`corpus.py bind-check` (after `lake build`) reads each result theorem's type and checks that its `Prop` hypotheses are exactly the argument's premise statements and its result type is the conclusion statement, matched by `lean_declaration` head constant; type and vocabulary parameters are not premises. A hypothesis whose head is a theory definition (`TruthCore.Comparison.*`) is a theory bundle: it is unfolded one step and split on `∧`, and each conjunct must bind to a listed premise, covering them exactly. A conclusion that is a theory definition is a consistency claim: its argument must list `commitment_statement_ids` (and may then have no premises), and these must match the conclusion's conjuncts in the same way. Keep non-theory conclusion propositions outside `TruthCore.Comparison`. During development, `corpus.py bind-check --result <ID>` (repeatable) or `--affected --base <BASE>` binds only the named or affected results and needs only their Solution modules built; the full `bind-check` (CI) also checks stale pins and registered models. `source_evidence.py check` verifies offline manifest and claim bindings. `source_evidence.py verify` fetches the exact pinned editions and rejects byte drift by Git blob SHA. Source fidelity remains a research/review judgment. Lean/Comparator verifies only the formal consequence.

Do not call an argument mechanically verified unless its result passes Comparator. CI also runs an independent no-`sorry` NanoDa check: over the whole built library on `main` pushes, nightly and manual runs, and on a PR over the modules its diff can affect (changed modules and their reverse dependents; `docs/axiom-policy.md`), so a failure a PR's scope missed still turns the next `main` run red.

### 8. Self-sweep before requesting review

Before requesting `@codex review`, apply the Review guidelines below to your own diff in one pass and fix what you find:

- every "read as" or attributed claim states no more than its cited sentence; any strengthening is stated as an explicit, unattributed open premise;
- **attribution self-check (#989), before the first push** (CI runs the same check on every PR): run `python3 scripts/corpus.py attribution-check --base <merge-base> --materialize`. For each new or changed stating claim (or claim whose statement text changed), it prints the premise next to the claim locator and the pinned passage text, and it fails until the claim records `"attribution": "The passage states X, which is the premise."` Check quantifier scope, species/genus restriction (one kind of cause or being read as all), and temporal and modal scope. If the sentence would be false, because the passage only bears on the premise or states something narrower, do not keep the claim as stating. Replace it by a `supports` relation with a gap note (#987), or state the narrower reading as its own statement;
- every load-bearing term on a root path links a definition through `definition_ids`;
- every ambiguous term links a disambiguation through `disambiguation_ids`.

**Claim vs type.** Most review P1s are prose saying more than the bound Lean type certifies. For every statement, argument or result the diff adds or changes, write in the PR body the prose next to the Lean type (statement paraphrase, claim interpretation, inference/argument `meaning`, result `description`, Lean doc comments, docs) and check:

- quantifiers and scope: "no", "not every", "some", "for all", "exists" (`¬ ∀` is not `∀ ¬`);
- modality and time;
- existence of a witness versus properties of the particular witness (a theorem about some model does not give the model's incidental properties);
- every hypothesis of the theorem is listed as a premise (including nonemptiness or satisfiability side conditions, so that no result is vacuous);
- conditions in the source (same-sense cause, restricted domain, "in any respect") survived into the Lean type;
- any condition added is not attributed to a source that does not state it; it is an explicit, unattributed open premise.

Each PR also reports its intended and actual change in root-path open premises, including "no change". The actual change is computed, not hand-written: link or paste the output of `python3 scripts/corpus.py frontier-diff --base <merge-base>` (conditional support bundles added or removed when comparable, per-route costs and reaching-root premises added, removed, or moved between bare, supported, stated and closed, and bare premises added), which CI prints to the job summary for every PR. Adding bare premises is listed for visibility, not as a regression (owner decision 2026-11-07). Route costs follow the [per-route open-premise cost rule](docs/corpus-model.md#premise-program-and-frontier) (`frontier --routes`): they diagnose an expanded proof, **not research progress**. A premise is established when it is self-evident with a met floor basis, defended (every recorded rival refuted by a verified refutation whose premises are all established, recursively and without circularity, #999), or derived from established premises; a stated or supported premise stays one leaf until it is established, so adding a derivation under it never raises a route's cost, while a derivation under a bare premise, or a new intermediate step, may raise it.

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

Corpus ids are opaque UUIDs (owner decision 2026-11-07): "we just cannot afford any ambiguity anymore". A readable id puts words, and therefore senses, into identity.

- **Never mint a readable id.** A new record gets a uuid4 (`python3 scripts/new_id.py`); `argument_batch.py` mints them for spec records.
- **Use labels for humans.** Every record has a `label`, unique within its kind, at most 100 characters, with no id-like text, naming the thing plainly (a statement by its proposition, an argument or result by its conclusion and route). A term with a linked disambiguated sense carries its sense tag: "Act is PRIOR_1 to potency".
- **Legacy readable ids are aliases.** Migrated records keep the old id as `legacy_id` (for example `STMT-CATHOLICISM-TRUE`, `PLATO-TIM-28A-CAUSE-A`); tools and prose may use it, and it resolves to exactly one uuid per kind. Tools accept a uuid, legacy id or label and print `label [uuid8]`.
- **IDs are permanent UUIDs; legacy aliases never change.** Labels may be improved at any time; docs/notes/label-cleanup.md lists the mechanical labels to fix, and that list may only shrink (#1233).
- An in-flight branch with readable-id records converts by merging `origin/main` and running `python3 scripts/migrate_uuid.py --write` (docs/notes/uuid-migration.md).

<!-- BEGIN:turborepo-agent-rules -->

# This is NOT the Turborepo you know

Turborepo configuration, task behavior, and CLI commands can vary between installed versions and may differ from your training data. Resolve the `turbo` package from this file's directory or relevant workspace; in monorepos, it may not be visible from the repository root. For example, run `node -p "require.resolve('turbo/package.json')"` from a workspace that depends on `turbo`.

Read `docs/README.md` inside that installed package first, then read the relevant pages from its `docs/` directory before changing Turborepo configuration or commands. Heed deprecation notices. These bundled docs match the installed package version and are available without network access.

This block is written and re-added by `turbo` before repository-scoped commands when an AI agent is detected. In the Turborepo source repository, its template is defined in `crates/turborepo-cli/src/cli/agent_guidance.rs`. Removing the managed block while updates are enabled means a later qualifying invocation will add it again. Set `"agentGuidance": false` in the root `turbo.json` or `turbo.jsonc` to opt out; this does not remove an existing block. Keep the block committed with your work to avoid an uncommitted change on the next agent invocation.
<!-- END:turborepo-agent-rules -->
