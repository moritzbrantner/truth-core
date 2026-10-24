# Corpus model

`truth-core` stores source witnesses, propositions, source readings, inference applications, arguments, and verification results as separate records.

## Core entities

- **Source** — bibliographic identity for a primary work together with its conventional citation system and CTS work identity.
- **Passage** — reproducible source evidence for a coherent range. A passage is tied to an exact digital edition snapshot by immutable revision and Git blob SHA and carries the extraction information needed to materialize the consulted text.
- **Statement** — an independently identified proposition. A statement is not owned by a source passage and is not marked true or verified merely because it exists.
- **Claim** — a scholarly/source claim that a passage supports a statement under a particular interpretation. Existing claim IDs remain stable provenance IDs. A formalized claim must resolve from its source ID and locator to exactly one passage witness. A claim read from a translated web snapshot carries `"basis": "translation"` (see `docs/source-evidence.md`).
- **Inference application** — one directed logical step with zero or more scoped assumptions, zero or more input statements, an inference rule label, and an output statement. An application with no inputs proves its output outright, as a theorem of logic.
- **Argument** — a composition of inference applications with advertised premise statements and a conclusion statement. An argument without premises advertises a theorem of logic (for example `LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `∀ p, ¬¬(p ∨ ¬p)`); its result's theorem then has no `Prop` hypotheses.
- **Result** — mechanical verification metadata connecting an argument to its Challenge/Solution theorem and Comparator configuration.
- **Relation** — optional additive metadata such as equivalence, contradiction, translation, strength, or attack. Relations never collapse entity identity.

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

There are three deliberately separate notions of verification:

1. **Source integrity** — `scripts/source_evidence.py` checks that every formalized claim resolves to one passage, that the passage belongs to the registered work, and that the fetched edition bytes match the pinned Git blob SHA. Materialization makes the consulted text reproducible.
2. **Source fidelity** — whether the claim is a defensible interpretation of the materialized passage in context. This remains scholarly/review judgment; materially different defensible readings should be stored separately.
3. **Formal verification** — Lean and Comparator establish that an advertised conclusion follows from advertised formal premises. They do not establish source fidelity or the historical truth of those premises.

No green status is allowed to collapse these boundaries. See `docs/source-evidence.md` for the source workflow.

## Composition and visualization

Large visual compositions should be derived from statements + inference applications + arguments. An argument can be collapsed to a single reusable block whose visible output is its conclusion, then expanded to reveal its internal premises and inference steps. React Flow or another graph renderer should consume such a derived projection; it should not become the canonical data model.

Source views should instead derive their evidence presentation from Source + Passage + Claim records so a reader can inspect the exact witness separately from the project's interpretation and from any later machine-checked argument.

## Premise program and frontier

The case for Catholicism (epic #143) has a root statement, `STMT-CATHOLICISM-TRUE`, reached by the verified skeleton argument `CATHOLICISM-SKELETON` from open premises. Long term, every premise should be either self-evident or have all its alternatives shown false. Three optional pieces of metadata record that status:

- **`self_evident`** on a statement: `{"justification_ids": ["..."]}`. Each ID must be a claim (for example a sourced *per se nota* reading, ST I q.2 a.1) or a result (for example a retorsion proof). Self-evidence is itself a sourced, challengeable claim, so a bare flag is rejected. An optional `note` states in prose what the marking rests on.

  The first marked node is `STMT-EXCLUDED-MIDDLE` (#167). Its self-evidence is **argued, not proved**: Aristotle states the law (*Metaphysics* IV.7, 1011b23-24) and defends it elenctically, from what an opponent grants by speaking significantly (IV.4, 1006a11-28; IV.7, 1012a17-24). Lean adds, without any axiom, that no instance can be denied (`LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`, `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`) and that the law is equivalent to double-negation elimination (`LOGIC-EXCLUDED-MIDDLE-IFF-DNE`). Lean does not prove excluded middle itself. Two alternatives are recorded: the denial of an instance (`STMT-SOME-EXCLUDED-MIDDLE-INSTANCE-FAILS`, ascribed by Aristotle to Anaxagoras), refuted by `LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE`; and intuitionist withholding (`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`), which those results do not refute and whose source waits for a witness.

  The two root-path instances, `STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT` and `STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT`, are derived from `STMT-EXCLUDED-MIDDLE` by results that only instantiate it. Those results are transcriptions (invariant 16) and close nothing by themselves; the instances are closed by rule (d) below, because their only premise is self-evident. They are not marked self-evident themselves.
- **Relations** with fixed endpoint kinds: `alternative_to` (statement → statement: the subject is a recorded alternative to the premise), `refutes` (argument → statement: the argument's conclusion shows the alternative false; it counts only when the argument has a result), `attacks` (statement, claim or argument → statement: a recorded objection), and `supports` (claim → statement: a source claim that bears on the premise without stating it, such as Dei Filius ch. 3 on the stage-3 premise; it is evidence, not an inference, and closes nothing).

`python3 scripts/corpus.py frontier` lists every statement used as a premise of some argument that is not closed. A statement is closed when it is (a) the conclusion of an argument with a verified result that is not a transcription, (b) marked `self_evident`, (c) refuted in every one of its recorded alternatives (at least one must be recorded), or (d) the conclusion of a transcription result (a single application of one hypothesis, invariant 16) whose argument premises are **all** closed by (a)–(d). Rule (d) is computed as a fixpoint, visiting transcription results in ID order, so the result recorded for each closure is deterministic (owner decision on #143, 2026-10-24). A conclusion verified only by transcriptions with some open premise stays open and is marked `open although proved`. Closures by (d) are listed in a `closed via transcription from closed premises` section (JSON: `closed_via_transcription`, with the result, argument, premises and path to the root). When the corpus has no `alternative_to` relations at all, the report says `no alternatives recorded`.

For each open premise it shows the arguments that use it directly, the transitive dependents (arguments and conclusions reached by repeatedly following the arguments that use a statement as a premise), one shortest path to the root, the attacking objections, and the supporting source claims. Items that reach the root come first, then items with more transitive dependents, then by ID, so the output is deterministic. Options:

- `--json` prints the same report as JSON;
- `--root STMT-...` chooses the statement whose path is shown (default `STMT-CATHOLICISM-TRUE`);
- `--reaching-root` keeps only the premises from which the root is reached.

Each open premise has a **depth**: `bare` when no claim states it and no `supports` relation points to it, otherwise `sourced` (sourced but undefended). The summary line gives both counts and `--json` adds `depth_counts`, plus `depth` and `stating_claims` per item; with `--reaching-root` the counts cover only the premises that reach the root. `/graph` tags open premises `frontier:bare` or `frontier:sourced` (#143, 2026-10-24; see `docs/systematic-corpus-loop.md`).

The report ends with a **transcription heuristics** section, and an open premise is marked `transcription premise of: ARG` when it is load-bearing in that sense. A result is flagged when its Solution proof (comments removed, leading `intro` steps ignored) is a single application of one hypothesis; when a hypothesis type, after unfolding its head definition one level and stripping leading `∀` binders, has the theorem's goal as the consequent of its last top-level `→`; or when the proof has at most two steps. Such a result certifies little more than the transcription of a bridge premise that already contains the conclusion. The checks are textual and deterministic: they can miss a transcription hidden behind further definitions, and a flagged one-step argument can still be faithful. With `--reaching-root` only results on a path to the root are listed.

The corpus explorer's `/graph` page applies the same rules in `apps/corpus-explorer/src/lib/proposition-graph.ts` and `lean-transcription.ts`; change both together. `scripts/testdata/frontier-transcription-closure.json` is a parity fixture read by both test suites, and the explorer tests also compare the real corpus with `corpus.py frontier --json`. Its `STAGE_CONCLUSIONS` list hardcodes the six stage statement IDs of `CATHOLICISM-SKELETON`, so keep those IDs stable or update the list.

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
transcription heuristics: 0 results flagged (single application, goal as premise consequent, or at most 2 proof steps)
```

Tests: `python3 -m unittest discover -s scripts -p 'test_*.py'`.
