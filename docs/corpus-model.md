# Corpus model

`truth-core` stores source witnesses, propositions, source readings, inference applications, arguments, and verification results as separate records.

## Core entities

- **Source** — bibliographic identity for a primary work together with its conventional citation system and CTS work identity.
- **Passage** — reproducible source evidence for a coherent range. A passage is tied to an exact digital edition snapshot by immutable revision and Git blob SHA and carries the extraction information needed to materialize the consulted text.
- **Statement** — an independently identified proposition. A statement is not owned by a source passage and is not marked true or verified merely because it exists.
- **Claim** — a scholarly/source claim that a passage supports a statement under a particular interpretation. Existing claim IDs remain stable provenance IDs. A formalized claim must resolve from its source ID and locator to exactly one passage witness. A claim read from a translated web snapshot carries `"basis": "translation"` (see `docs/source-evidence.md`).
- **Inference application** — one directed logical step with zero or more scoped assumptions, zero or more input statements, an inference rule label, and an output statement. An application with no inputs proves its output outright, as a theorem of logic.
- **Argument** — a composition of inference applications with advertised premise statements and a conclusion statement. An argument without premises (`"premise_statement_ids": []`) advertises a premise-free formal fact: a theorem of logic (for example `LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `∀ p, ¬¬(p ∨ ¬p)`), a countermodel or model (for example `AQUINAS-ST-I-Q2-A3-WEAK-READING-DOES-NOT-YIELD-UNMOVED-MOVER`), or a self-refutation proof showing an alternative contradictory. Its result's theorem then has no `Prop` hypotheses, and its conclusion is closed on the frontier without any external premise. Such a fact that another argument uses as a premise gets its own argument and result rather than an extra theorem name in that argument's Comparator config.
- **Result** — mechanical verification metadata connecting an argument to its Challenge/Solution theorem and Comparator configuration.
- **Relation** — optional additive metadata such as equivalence, contradiction, translation, strength, or attack. Relations never collapse entity identity.
- **Definition** (`corpus/definitions/`, `DEF-…`) — one sense of a term (#204): `term`, `definition`, and a `basis`. A `sourced` definition lists the `claim_ids` whose pinned passages give it. A `stipulative` one carries a `note` saying why it is stipulated and what would source it, and may still cite claims for context. An optional `lean_declaration` names the declaration or parameter that carries the sense. A definition is not a statement: it asserts nothing, and a nominal definition whose sufficiency an argument needs (such as `STMT-GOD-NAMES-THE-UNIQUE-MAXIME-ENS`) stays an open premise.
- **Disambiguation** (`corpus/disambiguations/`, `DISAMB-…`) — two or more senses of one term (`sense_definition_ids`) and a `resolution` saying which sense each use takes and why no argument passes from one sense to another. Some senses are recorded only for contrast (for example a strict greatest being next to *maxime ens*); those are stipulative and say so.

Statements, claims and arguments link the senses they use with `definition_ids`, and an ambiguity they must be read against with `disambiguation_ids`; an ambiguity is also reached through any linked definition that is one of its senses. `corpus.py check` rejects unknown links, a sourced definition without known claims, a stipulative one without a note, a disambiguation with fewer than two known senses, a definition that nothing links and no disambiguation lists, an argument whose conclusion, premises or commitments use two senses of one disambiguation without the argument linking it (mixing senses may be legitimate, but the argument must point to the resolution), and any `STMT-`, `DEF-` or `DISAMB-` id cited in definition or disambiguation prose that does not exist. Whether a term should be linked at all is a review judgment (AGENTS.md, Review guidelines).

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

## Identity and equivalence

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
`background_statement_ids` lists the ordered background. Optional
`remainder_statement_id` identifies cases admitted only by the weaker formula.
`evidence_result_ids` maps named obligations to existing result IDs; `separator`
names a closed application of the same specification and its result ID.
Metadata never establishes any of these obligations. The producer validates
canonical result/configuration bindings and uses Lean definitional equality for
complete theorem types, then the existing result verifiers. Computed labels are
derived presentation, not stored relation verdicts or a second proof authority.
See the [comparison design and current handoff](proposition-structure.md#current-handoff-certified-strength-comparisons)
for the obligation meanings, background boundaries and migration scope.

There are three deliberately separate notions of verification:

1. **Source integrity** — `scripts/source_evidence.py` checks that every formalized claim resolves to one passage, that the passage belongs to the registered work, and that the fetched edition bytes match the pinned Git blob SHA. Materialization makes the consulted text reproducible.
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

The case for Catholicism (epic #143) has a root statement, `STMT-CATHOLICISM-TRUE`, reached by the verified skeleton argument `CATHOLICISM-SKELETON` from open premises. Long term, every premise should be either self-evident or have all its alternatives shown false. Three optional pieces of metadata record that status:

- **`self_evident`** on a statement: `{"justification_ids": ["..."]}`. Each ID must be a claim (for example a sourced *per se nota* reading, ST I q.2 a.1) or a result (for example a retorsion proof). Self-evidence is itself a sourced, challengeable claim, so a bare flag is rejected. An optional `note` states in prose what the marking rests on.

  The floor is a **last resort** (owner decision #378, point 3: people disagree about what is self-evident). Prefer closing a premise by derivation or by refuting its alternatives, and mark it `self_evident` only when no other closure is available. Each marking also names its **floor basis** (#500, criteria of #497; no owner approval per premise). `corpus.py check` validates the shape per basis, and `corpus.py frontier` recomputes from the current relations, claims and results whether the criterion holds. A marking whose criterion fails closes nothing; `check` warns about it and the frontier item shows why.
  - `retorsion`: `justification_ids` are results and `denial_statement_id` names the denial, recorded as `alternative_to` the premise. Met when one of the results is not a transcription, its argument `refutes` the denial, and all of that argument's premises are closed (a retorsion resting on the premise itself closes nothing).
  - `common_ground`: `question_statement_id` names the disputed question and `positions` lists, per position, the proponent claims (`justification_ids` are exactly those claims). Met when the premise has no recorded `alternative_to`, the question has at least one, and the question and each of its current alternatives have a listed claim whose statement is the premise. Recording a new rival on the question, or one denying the premise, reopens it automatically.
  - `observation`: a justification claim states the premise, and every recorded alternative is listed in `sceptical_rival_ids` (global sceptical positions) and refuted by a counted refutation.

  Every marking except `common_ground` records the known disagreement in `disagreement` (#378): either `{"rival_statement_ids": [...], "claim_ids": [...]}`, naming the recorded rivals and/or the sourced claims that deny it is self-evident, or the literal `"none recorded"`. For `common_ground`, the recorded rivals' agreement is itself the disagreement record. A recorded `alternative_to` the premise that is missing from `rival_statement_ids` reopens the marking until the record is updated.

  `logical` is no basis: such a premise is proved and closes as a result. A marking without a basis is accepted only for the documented legacy list (`STMT-EXCLUDED-MIDDLE`), shown as basis `legacy`. `frontier` lists every marking with its basis under `floor` (`--json`: `floor`), the dossier shows the basis, and the root report (`frontier --routes`) says the root's closure is relative to the met floor bases that reach it.

  The first marked node is `STMT-EXCLUDED-MIDDLE` (#167). Its self-evidence is **argued, not proved**: Aristotle states the law (*Metaphysics* IV.7, 1011b23-24) and defends it elenctically, from what an opponent grants by speaking significantly (IV.4, 1006a11-28; IV.7, 1012a17-24). Lean adds, without any axiom, that no instance can be denied (`LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`) and that the law is equivalent to double-negation elimination (`LOGIC-EXCLUDED-MIDDLE-IFF-DNE`). Lean does not prove excluded middle itself. Two alternatives are recorded: the denial of an instance (`STMT-SOME-EXCLUDED-MIDDLE-INSTANCE-FAILS`, ascribed by Aristotle to Anaxagoras), refuted by `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`; and intuitionist withholding (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`), which those results do not refute. The remaining arguments of IV.7 (1011b29-1012a17) do not refute it either: each is aimed at a posited intermediate, and on its universal reading the thought argument (1012a2-5) is equivalent to excluded middle (`ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE`). Intuitionism is modeled as a complete rival theory, sourced from the SEP entry on intuitionism as a secondary witness (`SEP-INTUITIONISM`): it is consistent (`INTUITIONIST-THEORY-CONSISTENT`), it derives withholding from its account of assertion and proof (`INTUITIONISM-ENTAILS-EXCLUDED-MIDDLE-WITHHELD`), and its answer map in `TruthCore/Comparison/ExcludedMiddle.lean` records what it leaves unexplained, such as whether there is a first unmoved mover.

  The two root-path instances, `STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT` and `STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT`, are derived from `STMT-EXCLUDED-MIDDLE` by results that only instantiate it. Those results are transcriptions (invariant 16) and close nothing by themselves; the instances are closed by rule (d) below, because their only premise is self-evident. They are not marked self-evident themselves.
- **Relations** with fixed endpoint kinds: `alternative_to` (statement → statement: the subject is a recorded alternative to the premise), `refutes` (argument → statement: the argument's conclusion shows the alternative false; it counts only when the argument has a result and all of its premises are closed, see below), `attacks` (statement, claim or argument → statement: a recorded objection), `supports` (claim → statement: a source claim that bears on the premise without stating it, such as Dei Filius ch. 3 on the stage-3 premise; it is evidence, not an inference, and closes nothing), and `root_route` (argument → statement: the designated argument for a statement with several arguments; the argument must conclude that statement).
- **Unique statement identity.** Statement IDs are unique, and so are their `lean_declaration`s: one Lean declaration names exactly one statement, so an argument cites exactly the statement it uses (owner decision on #143, 2026-10-24). `corpus.py check` rejects a second statement with the same declaration. Two versions of a premise, such as the reduced and the fuller nominal definition of God, are two statements with two declarations.

`python3 scripts/corpus.py frontier` lists every statement used as a premise of some argument that is not closed. A statement is closed when it is (a) the conclusion of an argument with a verified result that is not a transcription, (b) marked `self_evident`, (c) refuted in every one of its recorded alternatives (at least one must be recorded), or (d) the conclusion of a transcription result (invariant 16, below) whose argument premises are **all** closed by (a)–(d). A `refutes` relation counts for (c) only when its argument has a verified result and is premise-free or has all of its premises closed by (a)–(d); a conditional refutation resting on an open premise refutes nothing yet (#391). Rules (c) and (d) are computed jointly as a fixpoint, visiting refutations by relation ID and transcription results by result ID, so the result recorded for each closure is deterministic (owner decision on #143, 2026-10-24). `--json` lists every refutation under `refutations` (with `counted` and its `open_premise_statement_ids`) and the alternatives they refute under `refuted_statements`; the text report lists the refutations that do not count, and `corpus.py check` warns about each.

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

For each open premise it shows the arguments that use it directly, the transitive dependents (arguments and conclusions reached by repeatedly following the arguments that use a statement as a premise), one shortest path to the root, the attacking objections, and the supporting source claims. When a statement has `root_route` relations, the walk enters it only through the designated arguments (owner decision on #143, 2026-10-24). The root `STMT-CATHOLICISM-TRUE` is routed through `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES`, so premises that only the older root compositions use do not count as reaching the root; they stay in the full frontier. Items that reach the root come first, then items with more transitive dependents, then by ID, so the output is deterministic. Options:

- `--routes` prints the **per-route open-premise cost** instead (with `--json`, the `routes` object that the full JSON report also carries). For each argument concluding the root it gives a cost, the number of distinct premises, whether the argument is verified, a transcription or the `root_route` designation, and marks the cheapest verified route (ties by argument ID). Each statement gets a set of **open leaves**, and its cost is that set's size. An established statement has none. A statement may stand as a single open leaf only when it is a genuine premise: a claim states it or a `supports` relation points to it (sourced), or no argument concludes it (bare). Any other statement, an intermediate conclusion such as `STMT-GOD-EXISTS`, is **expanded**: its leaves are the union of its premises' leaves under the verified non-transcription proof whose union is smallest. A transcription never expands a statement; it only makes its conclusion established through rule (d). An intermediate conclusion with no usable proof (only unverified or transcription arguments, or an ungrounded cycle) falls back to a leaf. A route's cost is the size of the union of its premises' leaf sets, listed in `open_premise_statement_ids` (sourced leaves that are themselves proved from open premises also appear in `proved_unestablished_statement_ids`). The minimum is chosen per statement and the unions are formed upward, so shared leaves count once but the choice is greedy, not an exact minimum set cover over the whole graph; the fixpoint only ever replaces a set by a strictly smaller one, so it terminates and is deterministic. A sourced premise always stays one leaf or becomes established, so **adding a derivation under a sourced premise never raises a route's cost** (owner decision on #391, 2026-10-26). A derivation under a bare premise, or a new intermediate step, is a relocation and may raise it. This is the official route count; do not compute it with ad-hoc scripts;
- `--json` prints the same report as JSON, plus `closed_statements` (each closed statement with the rule that closes it: `proved`, `self_evident`, `alternatives_refuted` or `via_transcription`) and `established_statements` (statements reached from self-evident or defended statements through verified results only; a closed statement proved from open premises is not established) and `reaching_root_statements` (every statement whose upward walk reaches the root, the root included; an open premise is listed exactly when its `path_to_root` is set). The GitHub Pages state view and graph read these (`docs/github-pages.md`);
- `--root STMT-...` chooses the statement whose path is shown (default `STMT-CATHOLICISM-TRUE`);
- `--reaching-root` keeps only the premises from which the root is reached.

Each open premise has a **depth**: `bare` when no claim states it and no `supports` relation points to it, otherwise `sourced` (sourced but undefended). The summary line gives both counts and `--json` adds `depth_counts`, plus `depth` and `stating_claims` per item; with `--reaching-root` the counts cover only the premises that reach the root. `/graph` tags open premises `frontier:bare` or `frontier:sourced` (#143, 2026-10-24; see `docs/systematic-corpus-loop.md`).

The report ends with a **transcription heuristics** section, and an open premise is marked `transcription premise of: ARG` when it is load-bearing in that sense. A result is flagged when its Solution proof (comments removed, leading `intro` steps ignored) is a single application of one hypothesis; when it only assembles hypotheses (an anonymous constructor or `And.intro` of hypotheses or their projections, possibly after `obtain`/`rcases` destructuring of hypotheses, or `constructor` followed only by `exact h` steps); when every explicit parameter is a `Prop` atom or a hypothesis and the hypotheses and goal relate only those atoms through connectives and definitions propositional over their parameters (opaque atoms); when a hypothesis type, after unfolding its head definition one level and stripping leading `∀` binders, has the theorem's goal as the consequent of its last top-level `→`; or when the proof has at most two steps. Such a result certifies little more than the transcription of a bridge premise that already contains the conclusion. Only single application and assembly make a result a transcription without a declaration; the opaque-atom flag warns in `corpus.py check` until the result declares `"transcription": "opaque_atoms"` (or its vocabulary is typed), and the other flags are advisory. The checks are textual and deterministic: they can miss a transcription hidden behind further definitions, and a flagged one-step argument can still be faithful. With `--reaching-root` only results on a path to the root are listed.

The JSON report also carries per-statement projections for views (#507), so no view recomputes corpus semantics: `statement_statuses` (one display status per statement, the first that applies: `proved` or `transcription`, `self-evident` only while the floor criterion holds, `defended`, `alternative`, `objection`, `open`, `derived` for an inference output some argument uses, else `source-only`; a status adds no closure rule), `floor` (each self_evident marking with its `basis`, whether its criterion is `met`, the `reasons` it fails, and its `disagreement`), `stages` and `statement_stages` (the stage conclusions of `CATHOLICISM-SKELETON` in `STAGE_CONCLUSIONS` of `scripts/corpus.py`, and for each statement the stages whose conclusion rests on it through inferences), `default_target` (the root when present, otherwise the verified conclusion resting on the most statements) and `premise_dependents` (the route-aware upward walk of every argument premise, closed ones included).

The corpus explorer reads all of these from `corpus.py frontier --json` (and dossiers from `corpus.py dossier --all --json`) and only joins them with the records for display (`apps/corpus-explorer/src/lib/proposition-graph.ts`). `scripts/testdata/frontier-transcription-closure.json` is a parity fixture read by both test suites, and one explorer test fails when the displayed closure or floor status of any real-corpus statement differs from an independent `corpus.py frontier --json` run. Keep the stage statement IDs stable or update `STAGE_CONCLUSIONS`.

The frontier is the work queue for the premise program, not a truth score: a premise leaves it only by being proved from other premises, marked self-evident with a justification, or having every recorded alternative refuted. The candidates list (`corpus.py next`) remains the queue for source ranges.

Example (abridged):

```text
$ python3 scripts/corpus.py frontier --reaching-root
frontier: 28 open premises: 8 bare, 20 sourced-undefended; root STMT-CATHOLICISM-TRUE

STMT-NO-INFINITE-PER-SE-MOVER-SERIES [sourced]
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
routes to STMT-CATHOLICISM-TRUE: 8 arguments; cheapest CATHOLICISM-SKELETON
cost  premises  argument
  28         9  CATHOLICISM-SKELETON  [cheapest]
  29        30  CATHOLICISM-FROM-QUARTA-VIA-WITH-CLASSICAL-ATTRIBUTES
  ...
  37        38  CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES  [designated]
  ...
open premises of the cheapest route CATHOLICISM-SKELETON (28):
  STMT-ACT-SIMPLY-PRIOR-TO-POTENCY
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
