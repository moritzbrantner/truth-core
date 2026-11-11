# Corpus model

`truth-core` stores source witnesses, propositions, source readings, inference applications, arguments, and verification results as separate records.

## Core entities

- **Source** — bibliographic identity for a primary work together with its conventional citation system and CTS work identity.
- **Passage** — reproducible source evidence for a coherent range. A passage is tied to an exact digital edition snapshot by immutable revision and Git blob SHA and carries the extraction information needed to materialize the consulted text.
- **Statement** — an independently identified proposition. A statement is not owned by a source passage and is not marked true or verified merely because it exists.
- **Claim** — a scholarly/source claim that a passage supports a statement under a particular interpretation. Existing claim IDs remain stable provenance IDs. A formalized claim must resolve from its source ID and locator to exactly one passage witness. A claim read from a translated web snapshot carries `"basis": "translation"` (see `docs/source-evidence.md`). A claim may carry an `attribution`: one sentence of the form "The passage states X, which is the premise." It records the worker's check that the cited passage states the statement, not something narrower (#989). `corpus.py check` validates its shape, and `corpus.py attribution-check --base <BASE>` requires it on every new or changed claim before the first push.
- **Inference application** — one directed logical step with zero or more scoped assumptions, zero or more input statements, an inference rule label, and an output statement. An application with no inputs proves its output outright, as a theorem of logic.
- **Argument** — a composition of inference applications with advertised premise statements and a conclusion statement. An argument without premises (`"premise_statement_ids": []`) advertises a premise-free formal fact: a theorem of logic (for example `LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `∀ p, ¬¬(p ∨ ¬p)`), a countermodel or model (for example `AQUINAS-ST-I-Q2-A3-WEAK-READING-DOES-NOT-YIELD-UNMOVED-MOVER`), or a self-refutation proof showing an alternative contradictory. Its result's theorem then has no `Prop` hypotheses, and its conclusion is closed on the frontier without any external premise. Such a fact that another argument uses as a premise gets its own argument and result rather than an extra theorem name in that argument's Comparator config.
- **Result** — mechanical verification metadata connecting an argument to its Challenge/Solution theorem and Comparator configuration.
- **Relation** — optional additive metadata such as equivalence, contradiction, translation, strength, or attack. Relations never collapse entity identity.
- **Definition** (`corpus/definitions/`, `DEF-…`) — one sense of a term (#204): `term`, `definition`, and a `basis`. A `sourced` definition lists the `claim_ids` whose pinned passages give it. A `stipulative` one carries a `note` saying why it is stipulated and what would source it, and may still cite claims for context. An optional `lean_declaration` names the declaration or parameter that carries the sense. A definition is not a statement: it asserts nothing, and a nominal definition whose sufficiency an argument needs (such as `STMT-GOD-NAMES-THE-UNIQUE-MAXIME-ENS`) stays an open premise.
- **Disambiguation** (`corpus/disambiguations/`, `DISAMB-…`) — two or more senses of one term (`sense_definition_ids`) and a `resolution` saying which sense each use takes and why no argument passes from one sense to another. Each sense also has a uuid identity and a `TERM_n` label (see Sense-indexed terms). Some senses are recorded only for contrast (for example a strict greatest being next to *maxime ens*); those are stipulative and say so.

Statements, claims and arguments link the senses they use with `definition_ids`, and an ambiguity they must be read against with `disambiguation_ids`; an ambiguity is also reached through any linked definition that is one of its senses. `corpus.py check` rejects unknown links, a sourced definition without known claims, a stipulative one without a note, a disambiguation with fewer than two known senses, a definition that nothing links and no disambiguation lists, an argument whose conclusion, premises or commitments use two senses of one disambiguation without the argument linking it (mixing senses may be legitimate, but the argument must point to the resolution), and any uuid or legacy `STMT-`, `DEF-` or `DISAMB-` id cited in definition or disambiguation prose that does not exist. Whether a term should be linked at all is a review judgment (AGENTS.md, Review guidelines).

### Definition dependencies and formal meaning

Disambiguation is **definition-driven**. A sense label such as `PRIOR_1` is an identity/display aid, not its meaning. Each consequential sense has its own definition record, with ordinary-language meaning, its precise Lean interpretation, and distinctions from neighboring senses. Where the meaning can be reduced to already typed concepts, give it a Lean definition with a body. Where a relation must remain primitive, mark that boundary explicitly: state its intended interpretation, parameters/domain, illustrative cases and exclusions, and the structural properties or bridges still **OPEN**. A Lean parameter, a fresh predicate with no body, or a theorem constraining it is not itself an explicit definition of its meaning. In particular, a definition record whose `lean_declaration` points at a constraining premise must identify that fact rather than present the premise as a definitional equation. Never turn a disputed philosophical assertion into a definitional equality just to make a proof succeed.

Definitions may introduce further technical terms that themselves require definitions and disambiguations. Follow this dependency chain as far as the *load-bearing meaning* requires; reuse existing `DEF-…` records, Lean vocabulary and Mathlib mathematics, and record relevant dependency IDs in existing definitions/notes or supported links. There is no fixed depth limit or objection to a substantial, reusable, mathlib-like philosophical dictionary. But not every ordinary explanatory word needs a new corpus record: expand when it affects an inference, rival comparison, source interpretation or independent reuse. An honest primitive is a valid boundary for conditional investigation, not a newly established philosophical truth. Keep definitional unfolding noncircular; cycles among arguments or semantic claims do not license circular Lean definitions. Treat contested relations between senses as explicit open bridges, proved relations or witnessed non-implications, never silent aliases.

For example, `DISAMB-PRIORITY-SIMPLE-OR-IN-TIME` separates `PRIOR_1` (simple/ontological priority, `DEF-SIMPLE-PRIORITY`), `PRIOR_2` (temporal priority, `DEF-PRIORITY-IN-TIME`) and `PRIOR_3` (priority in substance/perfection, `DEF-PRIORITY-IN-SUBSTANCE`). The current `PriorSimply`, `PriorInTime` and `PriorInSubstance` relations are distinct, but presently primitive; some linked Lean declarations are premises about those relations rather than their definitions. Their deeper formal interpretation and possible dependencies are therefore remaining work, not a consequence of having separate labels, types or a verified sense fork. See `docs/notes/load-bearing-terms.md` and the ongoing sense-indexing work (#1235).

**Sense forks.** A load-bearing ambiguous term on a root path should not leave its senses as unrelated silos. Its disambiguation may record a certified fork with three optional fields: `coverage_statement_id` (a statement that the listed senses are all the relevant ones), `exclusivity_statement_id` (a statement that exactly one sense applies to this use, formalized as the intended reading selecting one constructor of the sense enum, or as mutually exclusive cells, since senses may be strength-ordered) and `fork_result_ids` (verified joint theorems by cases over the sense enum). `corpus.py check` requires both statements to exist, to be distinct and to link the disambiguation in `disambiguation_ids`; each fork result must exist, link the disambiguation (argument or result `disambiguation_ids`) and take the coverage statement as a premise, so `fork_result_ids` needs `coverage_statement_id`. Each branch of the joint theorem either yields the route step or fails, the latter by a countermodel or a `refutes` relation; the conclusion then follows whichever sense applies. `truth orphans --senses` lists root-path disambiguations that lack any of the three parts. Without the fields it falls back to statements linking the disambiguation whose IDs end in `-SENSES-EXHAUSTIVE` (coverage) or `-SENSE-UNIQUE`/`-SENSES-EXCLUSIVE` (exclusivity), and a verified result taking that coverage premise. The fields record structure; they establish neither coverage nor exclusivity, which stay open premises until defended. See [certified forks](configuration-elimination-loop.md#certified-forks-for-selected-investigations).

A passage identifies evidence, not a proposition and not an interpretation. Multiple claims may legitimately use the same passage, and multiple mutually incompatible interpretations may coexist without changing the source witness.

## Provenance path

The intended source-derived path is:

```text
Source → Passage → Claim → Statement → Inference application → Argument → Result
```

The arrows are not all the same kind of relation. `Source → Passage` is bibliographic/evidential containment; `Passage → Claim` is interpretation; `Claim → Statement` associates that interpretation with an independently identified proposition; inference and result records then operate on propositions.

This separation prevents either provenance or proof status from becoming part of statement identity.

## Graph semantics

The canonical corpus is not a DAG. Statements can participate in arguments in either direction, and future semantic relations may be cyclic. A proof or explanation UI may derive an acyclic projection for one chosen derivation, but that projection is a view rather than the ontology.

Inference is never encoded as a bare statement-to-statement edge. For example, modus tollens is represented as two statement inputs (`P → Q` and `¬Q`) consumed by an explicit inference application that outputs `¬P`.

## Sense-indexed terms

Owner direction (2026-11-07): an argument's words may have several meanings, and the corpus tracks which meaning each argument uses. Every disambiguation names its term with a `term_label` (upper snake case: `PRIOR`) and gives each sense an entry in `senses`:

```json
"term_label": "PRIOR",
"senses": [
  {"id": "<uuid4>", "label": "PRIOR_1", "definition_id": "DEF-SIMPLE-PRIORITY"},
  {"id": "<uuid4>", "label": "PRIOR_2", "definition_id": "DEF-PRIORITY-IN-TIME"}
]
```

- **Senses are distinct Lean types.** Each sense names its own Lean predicate or type in `lean_declaration` (for example `…PriorSimply` against `…PriorInTime`), so equivocation is meant to be a type error the kernel and `bind-check` catch, not only a record mismatch. Within one disambiguation the declarations must be pairwise distinct; `corpus.py check` and `truth check` reject a sense without one, or sharing one with another sense, unless it is a legacy entry. The migration copied each sense's declaration from its definition record where that had one. A sense label without a distinct Lean declaration is not a finished sense.
- **Identity is the uuid.** A sense's `id` is an opaque uuid4; references (`term_senses`, `sense_bridges`, the allowlist) use it. The `TERM_n` label is for display and for tagging plain-language record labels ("Act is PRIOR_1 to potency"). Labels are stable: never renumber; a new sense is appended with the next index. `senses` lists the `sense_definition_ids` in the same order (kept for existing readers). A definition listed under one term label in several records keeps one uuid and label there. Compound records whose `term` names several words ("potency and mutability") received a shortened term label of at most six words (`scripts/sense_index.py`); splitting such a record into one disambiguation per word is the better long-term fix.
- **One sense per term per argument.** The senses an argument uses are derived from the `definition_ids` of the argument and of its conclusion, premise and commitment statements. Within one argument every disambiguated term resolves to exactly one sense. `corpus.py check` (and `truth check`) rejects an argument whose statements use, say, PRIOR_1 and PRIOR_2 unless it declares an **equivocation bridge**: `sense_bridges: [{"term": "PRIOR", "from": <uuid>, "to": <uuid>, "statement_id": "STMT-…"}]`, where the statement is one of the argument's premises and its content relates the two senses ("what is PRIOR_3 is PRIOR_1"). Owner decision (2026-11-08): an argument that derives such a relation declares its conclusion as the bridge, with `"statement_id": <the conclusion>, "role": "conclusion"` (the default role is `premise`). The bridges for a term must connect every sense it uses. A control or countermodel whose purpose is to show that mixing fails declares `sense_mixing_control: true`; it must have no premises and is exempt from the rule (no record kind identifies controls, so the flag is explicit).
- **`term_senses`.** An argument may record `term_senses: {"PRIOR": <uuid>}`; `argument_batch.py` writes it from the spec field `senses = {PRIOR = "PRIOR_1"}`. A declared sense must be a sense of that term and, when the argument's statements use the term, one of the senses they use.
- **Works with both senses: two arguments.** An argument valid in several senses is recorded once per sense, each with its own sense-specific statements, Lean theorem, `term_senses` and result. In a batch spec, `for_each_sense = {term = "PRIOR", senses = ["PRIOR_1", "PRIOR_3"]}` with one `[argument.cases.<SENSE>]` table per sense generates the per-sense arguments and results, each with a fresh uuid4 id and a `label` ("… [PRIOR_1]"); later runs reuse the ids by label and `term_senses`. All per-sense theorems may live in one Solution, whose generated Challenge freezes them together. A joint fork theorem over a sense enum (coverage and exclusivity premises, AGENTS.md "Connect every library to the case", item 4) remains an optional summary over the per-sense arguments; the per-sense arguments are primary.
- **Bind-level check.** `corpus.py bind-check` reads, for every result whose argument declares `term_senses`, the sense constants each hypothesis and the result type reach (`scripts/BindTypes.lean`): constants occurring in the elaborated type and in the values of `TruthCore` definitions it uses, unfolded transitively, stopping at sense constants and at library constants. The declared sense's constant must occur in a premise or the conclusion, and no hypothesis or result may reach another sense constant of the same term, except a hypothesis bound to a premise listed in `sense_bridges`, and the result type when the conclusion is a declared bridge. Each premise or conclusion statement that links the declared sense must reach that sense's constant in its own bound type: a statement whose declaration takes the sense predicate as a parameter (a God or sense predicate passed in) cannot bind to a theorem that instantiates it with another, say nominal, predicate. Controls are exempt. Two senses of one disambiguation whose constants are aliases (a definition whose eta-reduced value is the other constant) are also an error. This is a constant-occurrence heuristic: an opaque or axiomatized constant can hide a sense, and a sense reached through an unrelated definition is reported for review.
- **Legacy allowlists only shrink (#1233).** Arguments that already mixed senses, and senses without a distinct Lean declaration, when the rules were introduced are listed in `corpus/sense-index-allowlist.json` (`arguments`, `senses_without_lean_declaration`) and reported as warnings; anything else is an error. CI runs `python3 scripts/sense_index.py ratchet --base <merge-base>`, which fails when an entry is added and lists entries that no longer fail so they can be removed. `docs/notes/sense-index-migration.md` lists the entries (`python3 scripts/sense_index.py report --write`).
- **Display and naming.** `corpus.py dossier` and `context` show sense labels next to statements, definitions and arguments. `scripts/sense_labels.py` (`record_sense_labels`) returns any record's term → sense-label map, for naming and label checks.
- **Opaque ids for new records.** Validators that required a readable prefix (`DEF-`, `DISAMB-`, `MODEL-`, `ATTEMPT-`, `CONFIG-`, `scaffold_result.py --id`) also accept a lowercase uuid4, in Python and in `truth check`.

## Identity and equivalence

**Record ids are opaque uuids** (owner decision 2026-11-07, docs/decisions/2026-11-07-03-opaque-uuid-identity.md). A readable id such as `STMT-NOTHING-PRIOR-TO-ITSELF` put words, and therefore senses, into identity; it survives only as the record's `legacy_id`, an alias that never changes and is never minted again. Every record has:

- `id`: a uuid. A record migrated from a readable id has `uuid5(NAMESPACE, "<kind>:<legacy id>")` (`scripts/corpus_ids.py`), so any branch converts deterministically (docs/notes/uuid-migration.md); a new record has a `uuid4` (`python3 scripts/new_id.py`).
- `label`: the display name, required, at most 100 characters, unique within its kind, with no uuid-like or id-like text. It names the thing plainly: a statement by its proposition in short form, an argument or result by its conclusion and route. A term with a disambiguated sense the record links carries its sense tag (`Act is PRIOR_1 to potency`): untagged terms are an error for new records and a warning for the migrated records listed in docs/notes/label-cleanup.md. That list may only shrink (`scripts/label_cleanup.py`, #1233).
- `legacy_id` (migrated records only): the old readable id.

Tools accept a uuid, a legacy id or a label wherever they take an id (`--root`, `dossier`, `context`, `related`, `truth inspect`, …) and print records as `label [uuid8]` in text; JSON carries full uuids. Prose may cite records by legacy id (`STMT-…`, `DEF-…`, `DISAMB-…`) or uuid; `corpus.py check` resolves both. Record files keep their pre-migration names, and a migrated result's Comparator config stays at `results/<legacy id>/comparator.json`; new records live at `corpus/<kind>/<uuid>.json` and `results/<uuid>/comparator.json`. Lean declaration names are not corpus ids and do not change.

Statement IDs remain independent even when later evidence suggests two statements are textually identical, definitionally equal, logically equivalent, translation-equivalent, philosophically equivalent, or historically intended as the same thesis. Those are relations that can be added later. They do not mutate or merge existing IDs.

Passage identity is likewise not claim identity. Changing an interpretation does not mutate source evidence. Changing the underlying edition bytes requires a new pinned snapshot rather than silently changing what an existing evidence record points to.

## Verification boundaries

The [proposition structure inspector](proposition-structure.md) derives a bounded
expression view from elaborated Lean. Its internal addresses are scoped to the
statement and input revision, require no authored statement records, and carry
no frontier or proof status. Definition expansion, semantic interpretation and
argument support remain separate.

Selected strength comparisons use existing statement-to-statement relations
with predicate `strength_comparison`. Their single semantic owner is
`scripts/strength_comparisons.py`. The subject is the stronger proposition and
the object the weaker proposition; `comparison_spec` names the Lean
specification of their complete applications under shared parameters and
background. `delta_statement_id` names the proposed extra requirement;
`background_statement_ids` lists the ordered background.
`statement_parameter_indices` gives every named field (including `background.N`)
an explicit strictly increasing subsequence of the shared specification telescope,
counting implicit types and instances. Lean checks dependent argument types,
ordered argument equality and the full declaration application; specialization
and parameter permutations are outside this generic registration contract. Optional
`remainder_statement_id` identifies cases admitted only by the weaker formula.
`evidence_result_ids` maps named obligations to existing result IDs; `separator`
names a closed application of the same specification and its result ID.
Optional `explanatory_control_result_ids` links existing result authorities as
interpretive evidence only; these results never supply comparison certificate roles.
Metadata never establishes any of these obligations. The producer validates
canonical result/configuration bindings and uses Lean definitional equality for
complete theorem types, then the existing result verifiers. Computed labels are
derived presentation, not stored relation verdicts or a second proof authority.
See the [comparison design and prior delivery](proposition-structure.md#prior-delivery-certified-strength-comparisons)
for the obligation meanings, background boundaries and migration scope.

There are three deliberately separate notions of verification:

1. **Source integrity** — `scripts/source_evidence.py check` validates offline that every formalized claim resolves to one passage and that the passage belongs to the registered work. Explicit materialization of a selected passage checks its acquired bytes against the recorded pins. CI does not reacquire historical witnesses or certify their current availability.
2. **Source fidelity** — whether the claim is a defensible interpretation of the materialized passage in context. This remains scholarly/review judgment; materially different defensible readings should be stored separately.
3. **Formal verification** — Lean and Comparator establish that an advertised conclusion follows from advertised formal premises. They do not establish source fidelity or the historical truth of those premises.

No green status is allowed to collapse these boundaries. See `docs/source-evidence.md` for the source workflow.

For a single inference between **existing** statement IDs, `scripts/scaffold_result.py`
prepares linked inference, argument, result and Comparator drafts. For example,
after writing the intended meaning to `/tmp/result-meaning.txt`:

```bash
python3 scripts/scaffold_result.py --id MY-NEW-RESULT \
  --premise STMT-ACTUAL-MODAL-REFLEXIVITY \
  --conclusion STMT-ACTUAL-MODAL-REFLEXIVITY \
  --meaning-file /tmp/result-meaning.txt --rule instantiation \
  --challenge-module TruthCore.Results.MyResult.Challenge \
  --solution-module TruthCore.Results.MyResult.Solution \
  --theorem TruthCore.Results.MyResult.checks
```

This example only illustrates wiring; it supplies no proof. Default output is a
JSON preview. `--output-dir /tmp/my-result-drafts` instead creates a **new**
directory containing four canonical-path drafts and a manifest; existing output
directories, canonical paths and record IDs are rejected. The command never
creates or changes a statement or source claim. It copies meaning verbatim and
inherits definition/disambiguation links for manual review. No-premise arguments
omit `--premise`; repeated IDs and statements without a `lean_declaration` are
rejected. Scoped assumptions, consistency commitments and multiple inference
steps require manual records.

Optionally pass `--type-evidence /path/to/saved-bind-types.json`, an existing
`scripts/BindTypes.lean` JSON-array export. The command reuses `corpus.bind_result`
to compare the selected theorem's hypothesis/conclusion heads against the supplied
IDs and rejects mismatches. The manifest records the supplied bytes' hash and
comparison, not their provenance or freshness. It does not run Lean or establish
that an export came from the current revision. Without this option even head
alignment remains unchecked. No global type export is started.

The result draft intentionally lacks the required `status` field, so it is not
ready for corpus registration. Review the prose/type correspondence, premise
dossiers, inherited sense links and transcription classification; freeze the
Challenge before constructing its Solution, complete the record at the appropriate
workflow step, and run the normal final gates. Do not copy the manifest into the
corpus. Comparator permission defaults to zero axioms; explicit repeated `--axiom`
flags must satisfy the existing policy (the full approved three also require an
existing Solution importing Mathlib). Enabling NanoDa in a draft config does not
claim that NanoDa, Comparator, axiom inspection or source checks ran.

## Composition and visualization

Large visual compositions should be derived from statements + inference applications + arguments. An argument can be collapsed to a single reusable block whose visible output is its conclusion, then expanded to reveal its internal premises and inference steps. React Flow or another graph renderer should consume such a derived projection; it should not become the canonical data model.

Source views should instead derive their evidence presentation from Source + Passage + Claim records so a reader can inspect the exact witness separately from the project's interpretation and from any later machine-checked argument.

## Premise program and frontier

The case for Catholicism (epic #143) has a root statement, `STMT-CATHOLICISM-TRUE`, reached by the verified skeleton argument `CATHOLICISM-SKELETON` from open premises. The metadata and computations below describe formal frontier closure. The [systematic research loop](systematic-corpus-loop.md) separately assesses interpretation, premise warrant and overall provisional judgments; a computed closure label does not by itself establish philosophical truth. Three optional pieces of metadata record the frontier status:

- **`self_evident`** on a statement: `{"justification_ids": ["..."]}`. Each ID must be a claim (for example a sourced *per se nota* reading, ST I q.2 a.1) or a result (for example a retorsion proof). Self-evidence is itself a sourced, challengeable claim, so a bare flag is rejected. An optional `note` states in prose what the marking rests on.

  The floor is a **last resort** (owner decision #378, point 3: people disagree about what is self-evident). Prefer derivation or an adequately supported response to alternatives. Each marking names its **floor basis** (#500, criteria of #497). `corpus.py check` validates the shape per basis, and `corpus.py frontier` recomputes from the current relations, claims and results whether the criterion holds. Without the legacy approval override below, a marking whose criterion fails closes nothing; `check` warns and the frontier item shows why. Meeting a metadata criterion and defending the premise's interpretation and warrant remain distinct assessments.
  - `retorsion`: `justification_ids` are results and `denial_statement_id` names the denial, recorded as `alternative_to` the premise. Met when one of the results is not a transcription, its argument `refutes` the denial, and all of that argument's premises are established (#999; a retorsion resting on the premise itself, or on a premise merely proved from open premises, closes nothing).
  - `common_ground`: `question_statement_id` names the disputed question and `positions` lists, per position, the proponent claims (`justification_ids` are exactly those claims). Met when the premise has no recorded `alternative_to`, the question has at least one, and the question and each of its current alternatives have a listed claim whose statement is the premise. Recording a new rival on the question, or one denying the premise, reopens it automatically.
  - `observation`: a justification claim states the premise, and every recorded alternative is listed in `sceptical_rival_ids` (global sceptical positions) and refuted by a counted refutation.

  - **Legacy runtime compatibility: `owner_approval`** (#1007, decision 2026-11-05): `{"decision": "<issue-comment URL>", "date": "YYYY-MM-DD"}`. The existing computation treats an approved marking as met even when its ordinary basis criterion is unmet, for example while recorded rivals remain unrefuted. It still names a basis and requires a `disagreement` record, including for `common_ground`. Such an item needs no pinned stating text or basis record (`positions`, `denial_statement_id`, `sceptical_rival_ids`); its `justification_ids` may be the closest supporting texts/results, and any supplied basis field must name known statements. The unmet criterion remains visible as `criterion_reasons` and as "met by owner approval … (criterion not met: …)". An omitted newly recorded rival reopens the marking. These are compatibility rules describing existing metadata, not independent philosophical warrant or rival elimination. **Do not create new approval-only closures or translate provisional judgments into `owner_approval`.** The 2026-11-10 method changes no schema, existing marking or computed status. Inspect the current frontier for the actual inventory.

  Every marking except `common_ground` records the known disagreement in `disagreement` (#378): either `{"rival_statement_ids": [...], "claim_ids": [...]}`, naming the recorded rivals and/or the sourced claims that deny it is self-evident, or the literal `"none recorded"`. For `common_ground`, the recorded rivals' agreement is itself the disagreement record. A recorded `alternative_to` the premise that is missing from `rival_statement_ids` reopens the marking until the record is updated.

  `logical` is no basis: such a premise is proved and closes as a result. A marking without a basis is accepted only for the documented legacy list (`STMT-EXCLUDED-MIDDLE`), shown as basis `legacy`. `frontier` lists every marking with its basis under `floor` (`--json`: `floor`), the dossier shows the basis, and the root report (`frontier --routes`) says the root's closure is relative to the met floor bases that reach it.

  The first marked node is `STMT-EXCLUDED-MIDDLE` (#167). Its self-evidence is **argued, not proved**: Aristotle states the law (*Metaphysics* IV.7, 1011b23-24) and defends it elenctically, from what an opponent grants by speaking significantly (IV.4, 1006a11-28; IV.7, 1012a17-24). Lean adds, without any axiom, that no instance can be denied (`LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`) and that the law is equivalent to double-negation elimination (`LOGIC-EXCLUDED-MIDDLE-IFF-DNE`). Lean does not prove excluded middle itself. Two alternatives are recorded: the denial of an instance (`STMT-SOME-EXCLUDED-MIDDLE-INSTANCE-FAILS`, ascribed by Aristotle to Anaxagoras), refuted by `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`; and intuitionist withholding (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`), which those results do not refute. The remaining arguments of IV.7 (1011b29-1012a17) do not refute it either: each is aimed at a posited intermediate, and on its universal reading the thought argument (1012a2-5) is equivalent to excluded middle (`ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE`). Intuitionism is modeled as a complete rival theory, sourced from the SEP entry on intuitionism as a secondary witness (`SEP-INTUITIONISM`): it is consistent (`INTUITIONIST-THEORY-CONSISTENT`), it derives withholding from its account of assertion and proof (`INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD`), and its answer map in `TruthCore/Comparison/ExcludedMiddle.lean` records what it leaves unexplained, such as whether there is a first unmoved mover.

  The two root-path instances, `STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT` and `STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT`, are derived from `STMT-EXCLUDED-MIDDLE` by results that only instantiate it. Those results are transcriptions (invariant 16) and close nothing by themselves; the instances are closed by rule (d) below, because their only premise is self-evident. They are not marked self-evident themselves.
- **Relations** with fixed endpoint kinds: `alternative_to` (statement → statement: the subject is a recorded alternative to the premise), `refutes` (argument → statement: the argument's conclusion shows the alternative false; it counts only when the argument has a result and all of its premises are closed, see below), `attacks` (statement, claim or argument → statement: a recorded objection), `supports` (claim → statement: a source claim that bears on the premise without stating it, such as Dei Filius ch. 3 on the stage-3 premise; it is evidence, not an inference, and closes nothing), `root_route` (argument → statement: the designated argument for a statement with several arguments; the argument must conclude that statement), and `strengthens` (statement → statement: the strong version entails the weak one, backed by a verified result; see Strength order below).
- **Unique statement identity.** Statement IDs are unique, and so are their `lean_declaration`s: one Lean declaration names exactly one statement, so an argument cites exactly the statement it uses (owner decision on #143, 2026-10-24). `corpus.py check` rejects a second statement with the same declaration. Two versions of a premise, such as the reduced and the fuller nominal definition of God, are two statements with two declarations.

`python3 scripts/corpus.py frontier` lists every statement used as a premise of some argument that is not closed. A statement is closed when it is (a) the conclusion of an argument with a verified result that is not a transcription, (b) marked `self_evident`, (c) refuted in every one of its recorded alternatives (at least one must be recorded), or (d) the conclusion of a transcription result (invariant 16, below) whose argument premises are **all** closed by (a)–(d). A `refutes` relation counts for (c) only when its argument has a verified result and is premise-free or has all of its premises **established** (#391, #999): self-evident with a met floor basis, defended (rule (c)), or the conclusion of a verified result whose premises are all established, recursively. A premise that is closed only because it is proved from open premises does not suffice, so a conditional refutation resting on an open premise, directly or through such a proof, refutes nothing yet. Rules (b)–(d), `established` and the strength-order propagation (#1017, below) are computed jointly as a least fixpoint, so no circular support counts (two refutations each resting on the premise the other would defend establish nothing), visiting refutations by relation ID and transcription results by result ID, so the result recorded for each closure is deterministic (owner decision on #143, 2026-10-24). `--json` lists every refutation under `refutations` (with `counted`, its `open_premise_statement_ids` and the `unestablished_premise_statement_ids` that keep a verified refutation from counting) and the alternatives they refute under `refuted_statements`; the text report lists the refutations that do not count, and `corpus.py check` warns about each.

**Strength order** (#1017). When a proposition or premise is ambiguous in strength, both versions are sibling statements (for example `STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-STRONG`, closure for every sentence, and `-WEAK`, closure for negated sentences only). A `strengthens` relation (**statement → statement**: the subject is the strong version, the object the weak one) records that the strong version entails the weak one. It needs `verification_result_id`, a verified result whose argument has exactly the strong version as its only premise and the weak version as its conclusion, so `bind-check` binds the entailment to both declarations like any other result; and a nonempty `note`. An optional `strictness_result_id` names a verified premise-free result (a countermodel) showing that the weak version does not entail the strong one. `corpus.py check` rejects a registration without such a result, a reverse or duplicate pair (equivalent versions use `logically_equivalent_to`), and a backing result used twice. The heavier `strength_comparison` certificates above are presentation only; `strengthens` is the order the frontier uses.

In `frontier` the backing argument is a **registration, not a route step**: it is set aside before closure is computed, so it closes nothing by rules (a) or (d), does not make the strong version a premise of anything, and is not walked to the root or expanded in route costs. Otherwise a weak version would close from an open strong sibling, and circularly when the weak version is also a premise of a proof of the strong one (as for the mandate-scope pair, where the weak version and stage 6 prove the strong one). Instead, inside the same least fixpoint as closure and `established`:

- an **established** strong version establishes and closes the weak one (closure label `via_strength`);
- a **refuted** weak version (one with a counted refutation, or itself refuted this way) refutes the strong one, by contraposition, so a premise whose recorded alternative is the strong version can be defended by refuting the weak one;
- neither runs in reverse: an established weak version establishes nothing, and a refuted strong version refutes nothing.

A strong version that is merely closed (proved from open premises) leaves the weak one open. `--json` lists every registered pair under `strength_order` with `weak_established_via_strength` and `strong_refuted_via_strength`; the text report lists them under `strength order`. Attribution stays per version: depth, floor criteria and `attribution-check` read only the claims whose `statement_id` is that version, so a claim stating the weak version never makes the strong one stated.

Each argument should use the **weakest version that suffices**: it makes the argument stronger and the premise easier to defend. An argument that keeps a strong version with a registered weak sibling records why in `strong_version_needed` (`{"STMT-…-STRONG": "reason"}`; each key must be a premise and the subject of a `strengthens` relation). `corpus.py check` warns, one line per strong version, about the arguments that use it without that field. Whether the weak version would actually suffice needs a proof attempt, so the warning only asks for the declaration and the judgment is a review rule: a reviewer who sees a strong version where the registered weak one suffices reports it, and a reason in `strong_version_needed` that a proof refutes is a P1. Floor items say in their marking's `note` which version the defeat needs.

`instance_of_schema` is a separate **statement → statement** registration
relation (#412). It requires a nonempty `note`, a known
`verification_result_id`, and named `instance_theorem` and `schema_theorem`
obligations listed in that result's Comparator configuration. The instance and
schema each have their own statement declaration. `bind-check` reuses its
normal theorem-type checker for both obligations: the result head must match
the corresponding statement and no extra proposition hypothesis is permitted.
Conditional philosophical requirements therefore belong inside the advertised
statement, not as unlisted assumptions of its registration proof. Run that
result's Comparator/NanoDa gate before advertising the instance as verified.
Offline metadata validation alone proves neither theorem. The result may
certify a shared package and multiple separate obligations in one configuration.

Registration never acts as source support, inference, refutation or frontier
closure; it does not modify `supports` or its claim-only endpoint contract.
It also does not infer the universal schema from an instance. Schema campaigns
can use this contract once their separate proof obligations have been checked.

A result is a **transcription** (invariant 16) when its record declares one in the optional `transcription` field, or when the Lean heuristics below find a single application of one hypothesis or a pure assembly of hypotheses. The field takes one kind: `opaque_atoms` (every proposition the theorem relates is an unconstrained `Prop` parameter, or a definition propositional over such parameters), `single_application` (the proof applies one premise whose consequent is the conclusion), `assembly` (the proof only pairs or destructures hypotheses, such as `⟨hClaims, hRose⟩`), or `instantiation` (the proof only instantiates a general premise or lemma at the case). `corpus.py check` rejects any other value and requires the field when the `description` opens with a transcription label (`Transcription`, `Opaque-atom transcription`, `Near-transcription`, `Logical transcription`); the prose explains, the field decides (#391). `--json` lists all of them in `transcription_results` (`kind`, and whether it was `declared`). A conclusion verified only by transcriptions with some open premise stays open and is marked `open although proved`. Closures by (d) are listed in a `closed via transcription from closed premises` section (JSON: `closed_via_transcription`, with the result, argument, premises and path to the root). When the corpus has no `alternative_to` relations at all, the report says `no alternatives recorded`.

For each open premise it shows the arguments that use it directly, the transitive dependents (arguments and conclusions reached by repeatedly following the arguments that use a statement as a premise), one shortest path to the root, the attacking objections, and the supporting source claims. When a statement has `root_route` relations, the walk enters it through the designated arguments and through any verified non-transcription argument concluding it, but not through an unverified or transcription one. This is the owner decision of 2026-11-07 ("reach the root via any verified route"), which supersedes the 2026-10-24 rule on #143 under which only the designated arguments were walked. The root `STMT-CATHOLICISM-TRUE` is routed through `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES`. That designated route stays the headline for reporting and comparisons (`--routes` marks it `[designated]`; `frontier-diff` reports it), while premises of the other verified root compositions now also reach the root. Items that reach the root come first, then items with more transitive dependents, then by ID, so the output is deterministic. Options:

- `--routes` prints the **per-route expanded open-leaf cost diagnostic** instead (with `--json`, the `routes` object that the full JSON report also carries). For each argument concluding the root it gives a cost, the number of distinct premises, whether the argument is verified, a transcription or the `root_route` designation, and marks the cheapest verified route (ties by argument ID). Each statement gets a set of **open leaves**, and its cost is that set's size. An established statement has none. A statement may stand as a single open leaf only when it is a genuine premise: a claim states it (stated; supported when every stating claim is bibliographic or on an unavailable witness) or a `supports` relation points to it (supported), or no argument concludes it (bare). Any other statement, an intermediate conclusion such as `STMT-GOD-EXISTS`, is **expanded**: its leaves are the union of its premises' leaves under the verified non-transcription proof whose union is smallest. A transcription never expands a statement; it only makes its conclusion established through rule (d). An intermediate conclusion with no usable proof (only unverified or transcription arguments, or an ungrounded cycle) falls back to a leaf. A route's cost is the size of the union of its premises' leaf sets, listed in `open_premise_statement_ids` (stated or supported leaves that are themselves proved from open premises also appear in `proved_unestablished_statement_ids`). Each route also gives `open_premise_depths` (each leaf's depth, or `proved_unestablished`) and `depth_counts` (leaves by `bare`, `supported`, `stated` and `proved_unestablished`), and the text output has a column for each of the three depths and one (`proved`) for leaves proved from open premises, so the four columns sum to the cost (#987). The minimum is chosen per statement and the unions are formed upward, so shared leaves count once but the choice is greedy, not an exact minimum set cover over the whole graph; the fixpoint only ever replaces a set by a strictly smaller one, so it terminates and is deterministic. A stated or supported premise always stays one leaf or becomes established, so **adding a derivation under such a premise never raises a route's cost** (owner decision on #391, 2026-10-26). A derivation under a bare premise, or a new intermediate step, is a relocation and may raise it. This is the canonical expanded-route diagnostic, **not a research-progress KPI**. An argument from `A` and `B` to open `P1` introduces another way to support `P1`, even if this expansion changes cost 1 → 2;
- `--json` also carries `support_options`: every root-reaching statement used as an argument premise has a **direct-assumption option when unestablished**, and distinct verified non-transcription arguments concluding it are grouped by their premise-ID set as **conditional support alternatives** (with argument IDs). Counts distinguish how many *unestablished* premises have alternatives from the number of unique premise bundles across all such statements (including established conclusions, so settlement does not erase support credit); duplicate proofs of the same obligation set do not inflate the count. A direct self-dependent argument does not count. An unverified or transcription-only argument is not counted as substantive support. A verified conditional inference **does not establish its antecedents** or prove independence of the alternatives; a new bundle is evidence of added argumentative optionality, not of new foundational closure. The primary settlement measure remains `established_statements`, with open obligations and conditional alternatives reported alongside it;
- `--json` prints the same report as JSON, plus `closed_statements` (each closed statement with the rule that closes it: `proved`, `self_evident`, `alternatives_refuted`, `via_strength` (an established strong version, #1017) or `via_transcription`) and `established_statements` (statements reached from self-evident or defended statements through verified results only, where defended counts only refutations from established premises; a closed statement proved from open premises is not established) and `reaching_root_statements` (every statement whose upward walk reaches the root, the root included; an open premise is listed exactly when its `path_to_root` is set). The GitHub Pages state view and graph read these (`docs/github-pages.md`);
- `--root STMT-...` chooses the statement whose path is shown (default `STMT-CATHOLICISM-TRUE`);
- `--reaching-root` keeps only the premises from which the root is reached.

Each open premise has a **depth** (#143, 2026-10-24; three categories by owner decision on #987, 2026-11-05):

- `stated`: a claim on a pinned source states it, that is, a claim on a passage with pinned bytes (a text witness, web snapshot or media span) has it as its `statement_id`;
- `supported`: no claim on a pinned source states it, but a `supports` relation points to it (a source claim bears on it without stating it, and the relation's `note` records the gap; `corpus.py check` warns about a `supports` relation without a note), or only claims that cannot be byte-verified state it: claims on a `bibliographic_span` (cited by page, no pinned bytes) or on a permanently unavailable web snapshot (`witness: "unavailable"`, bytes no longer re-verifiable; owner decisions 2026-11-05). Such a premise becomes `stated` once its witness is pinned;
- `bare`: neither.

Stated and supported premises are both undefended; the depth says how close a source comes to the premise, not that it is justified. A premise both stated and supported is `stated`. A premise stated only by such claims is `supported`; it keeps them under `stating_claims` and also lists them under `bibliographic_claims` or `unavailable_claims` (not byte-verified). It becomes `stated` once a (new) witness is pinned. The summary line gives the three counts and `--json` adds `depth_counts` (`bare`, `supported`, `stated`), plus `depth`, `stating_claims` and `supporting_claims` per item; with `--reaching-root` the counts cover only the premises that reach the root. `/graph` tags open premises `frontier:bare`, `frontier:supported` or `frontier:stated` (see `docs/systematic-corpus-loop.md`).

`frontier-diff --base <REV> [--head <REV>]` compares the reaching-root frontier of two revisions (#948): open premises added, removed or moved between `bare`, `supported`, `stated` and `closed`; the open counts by depth; the cheapest **expanded** route; and each changed route's cost with its leaves by depth. It reports distinct verified conditional support bundles added or removed when both revisions carry the projection. A revision with an older `corpus.py` lacking `support_options` is **not** treated as having zero alternatives. It also lists **bare premises added**: every premise that is bare at the head and was not bare at the base (added bare, or moved to bare from closed, supported or stated). They are listed for visibility, not as a regression (owner decision 2026-11-07). `supported` premises stay in their own column so a supports-only relocation is not reported as a stated one. A revision older than #987 reports `sourced`; the diff splits it into `stated` (the item has a stating claim that is neither bibliographic nor on an unavailable witness) or `supported` (it has none).

`thickness [--base <REV>] [--json]` reports **derivational thickness**: for each statement from which the root is reached, the verified non-transcription arguments that conclude it, with the counts of statements derived at least once and at least twice. Route costs follow only the cheapest derivation of each node, and a stated or supported premise stays one leaf however many proofs it has, so an alternative derivation need not change route cost. `thickness` counts arguments; `frontier-diff` compares distinct support bundles when available. With `--base` it lists the statements whose derivation set changed. It is presentation only: it closes nothing and changes no route cost.

`thickness --queue [--json]` is the **derivation worklist**: every statement reaching the root with no verified non-transcription derivation, with its frontier depth, `lean_declaration`, each argument concluding it and its status (verified, transcription kind, or no result), the `supports` relations pointing to it, its `alternative_to` rivals with their `refutes` arguments and whether the frontier counts them, the attempts naming it, and up to five definition-linked unused statements (the statement of a claim cited by a definition, used by no argument, sharing a definition with the target). A statement named by an attempt with outcome `rejected` is marked examined. Unexamined statements come first, then those with the most dependent arguments. Like `thickness`, it closes nothing.

The report ends with a **transcription heuristics** section, and an open premise is marked `transcription premise of: ARG` when it is load-bearing in that sense. A result is flagged when its Solution proof (comments removed, leading `intro` steps ignored) is a single application of one hypothesis; when it only assembles hypotheses (an anonymous constructor or `And.intro` of hypotheses or their projections, possibly after `obtain`/`rcases` destructuring of hypotheses, or `constructor` followed only by `exact h` steps); when every explicit parameter is a `Prop` atom or a hypothesis and the hypotheses and goal relate only those atoms through connectives and definitions propositional over their parameters (opaque atoms); when a hypothesis type, after unfolding its head definition one level and stripping leading `∀` binders, has the theorem's goal as the consequent of its last top-level `→`; or when the proof has at most two steps. Such a result certifies little more than the transcription of a bridge premise that already contains the conclusion. Only single application and assembly make a result a transcription without a declaration; the opaque-atom flag warns in `corpus.py check` until the result declares `"transcription": "opaque_atoms"` (or its vocabulary is typed), and the other flags are advisory. The checks are textual and deterministic: they can miss a transcription hidden behind further definitions, and a flagged one-step argument can still be faithful. With `--reaching-root` only results on a path to the root are listed.

The JSON report also carries per-statement projections for views (#507), so no view recomputes corpus semantics: `statement_statuses` (one display status per statement, the first that applies: `proved` or `transcription`, `self-evident` only while the floor criterion holds, `defended`, `alternative`, `objection`, `open`, `derived` for an inference output some argument uses, else `source-only`; a status adds no closure rule), `floor` (each self_evident marking with its `basis`, whether its criterion is `met`, the `reasons` it fails, and its `disagreement`), `stages` and `statement_stages` (the stage conclusions of `CATHOLICISM-SKELETON` in `STAGE_CONCLUSIONS` of `scripts/corpus.py`, and for each statement the stages whose conclusion rests on it through inferences), `default_target` (the root when present, otherwise the verified conclusion resting on the most statements) and `premise_dependents` (the route-aware upward walk of every argument premise, closed ones included).

The corpus explorer reads all of these from `truth frontier --json` (and dossiers from `truth dossier --all --json`), the Rust CLI's semantic-field-compatible ports of the `corpus.py` commands (frontier adds `input_identity`; the all-dossiers report remains a statement-ID map), and only joins them with the records for display (`apps/corpus-explorer/src/lib/proposition-graph.ts`). `scripts/testdata/frontier-transcription-closure.json` is a parity fixture read by both test suites, and one explorer test fails when the displayed closure or floor status of any real-corpus statement differs from an independent `truth frontier --json` run; the `truth-cli` CI job keeps that report at parity with `corpus.py frontier --json`. The fixture tests above still call Python's `frontier_report` directly (`src/lib/frontier-fixture.ts`). Keep the stage statement IDs stable or update `STAGE_CONCLUSIONS`.

The frontier is a diagnostic input to the master's research queue, not a truth score or a complete research priority order. A premise leaves it under the closure rules above, which can include a conditional proof or legacy floor marking. Dossiers, attempts, source candidates and the current handoff also inform selection under the [systematic loop](systematic-corpus-loop.md#priority-and-cumulative-progress). `corpus.py next` retains its existing source-range queue behavior. Provisional judgments affect research decisions and qualified reports without changing these computed statuses.

Example (abridged):

```text
$ python3 scripts/corpus.py frontier --reaching-root
frontier: 91 open premises: 33 bare, 17 supported, 41 stated; root STMT-CATHOLICISM-TRUE

STMT-NO-INFINITE-PER-SE-MOVER-SERIES [stated]
  A per se ordered series of moved movers cannot go on to infinity: ...
  dependent arguments: 3 (AQUINAS-ST-I-Q2-A3-PRIMA-VIA, AQUINAS-ST-I-Q2-A3-PRIMA-VIA-RELATIVE, CATHOLICISM-FROM-PRIMA-VIA)
  transitive dependents: 5 arguments, 4 statements
  path to root: STMT-NO-INFINITE-PER-SE-MOVER-SERIES -> CATHOLICISM-FROM-PRIMA-VIA -> STMT-CATHOLICISM-TRUE
  objections: none recorded
  stating source claims: AQUINAS-ST-I-Q2-A3-NO-INFINITE-REGRESS-A
...
closed via transcription from closed premises: 2 statements (a transcription result whose premises are all closed)
  STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT: closed via transcription CATHOLICISM-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT-FROM-EM from closed premises (STMT-EXCLUDED-MIDDLE)
  ...
transcription heuristics: 0 results flagged (single application, assembly of hypotheses, opaque Prop atoms, goal as premise consequent, or at most 2 proof steps)

$ python3 scripts/corpus.py frontier --routes
routes to STMT-CATHOLICISM-TRUE: 12 arguments; cheapest CATHOLICISM-FROM-QUARTA-VIA-WITHOUT-TRUTH-BRIDGE
cost  bare  supported  stated  proved  premises  argument
  31     1         11      11       8        29  CATHOLICISM-FROM-QUARTA-VIA-WITHOUT-TRUTH-BRIDGE  [cheapest]
  31     3         10       5      13         9  CATHOLICISM-SKELETON
  ...
  40     1         11      17      11        38  CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES  [designated]
  ...
open premises of the cheapest route CATHOLICISM-FROM-QUARTA-VIA-WITHOUT-TRUTH-BRIDGE (31):
  STMT-ACT-SIMPLY-PRIOR-TO-POTENCY [stated]
  STMT-BRIDGE-GOD-FOUNDED-AUTHORITY-PROPOSES-ONLY-TRUTH [supported]
  ...
  STMT-GOD-IS-ETERNAL (proved, rests on open premises)
  ...
```

Tests: `python3 -m unittest discover -s scripts -p 'test_*.py'`.

## Research attempts and premise dossiers (#413)

`corpus/attempts/` records attempted research against existing statement IDs. An
attempt is not a philosophical entity, a claim or an inference, and its outcome
does not affect closure. `corpus.py check` validates its targets, local result/claim
evidence, outcome, kind and date. PR references use canonical `PR-<number>` syntax
and are not fetched by the offline check.

`corpus.py dossier <STMT-ID>` and the explorer's statement-linked dossier collect
the existing meanings, sources, arguments, alternatives, attempts and exact
route-leaf membership without adding another calculation of truth or closure.
See [Premise dossiers and research attempts](premise-dossiers.md) for the contract.
