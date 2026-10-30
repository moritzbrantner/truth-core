# Modal logic MVP

This slice adds a small, mechanically checked laboratory for normal propositional modal logic without changing the source-corpus model.

## Purpose

The MVP should make three different things visible without conflating them:

1. **Modal syntax** — propositions can be qualified by necessity (`□`) and possibility (`◇`).
2. **Kripke semantics** — truth is evaluated at a world relative to an accessibility relation and an atomic valuation.
3. **Frame restrictions** — adding modal axioms restricts the admissible accessibility relations, producing the familiar modal cube.

The frontend is an explorable model of those semantics. Lean is the verification boundary for the generic correspondence direction implemented here and for the concrete S4 example.

## Reference and evidence boundary

The original MVP is mathematics, not a source-derived corpus claim, and introduced no `corpus/` records. The later graph and convergence certificates assemble mathematical library results into canonical verification records; they introduce no source-attributed philosophical claim. The frame-condition ⇒ axiom-validity direction of the correspondences below is established by the Lean proofs in `TruthCore/Modal/` (the later path-based converse results are itemized below), not by citation, so the AGENTS.md source-materialization invariants for source-derived claims do not apply.

The Stanford Encyclopedia of Philosophy entry [“Modal Logic”](https://plato.stanford.edu/entries/logic-modal/) (substantive revision 23 January 2023) supplies orientation, not proof evidence. The original MVP followed sections 7–8; the coverage audit below checks the whole entry against existing repository modules. If a later slice attributes a modal thesis to a source (for example Aristotle's modal syllogistic), that slice must add a pinned `corpus/passages/` witness and follow the ordinary atomic loop.

The SEP map uses **M** for the reflexivity axiom `□A → A`; the code uses the more common label **T**. The correspondence is otherwise the same:

| Axiom | Formula | Frame condition |
| --- | --- | --- |
| D | `□A → ◇A` | serial |
| T / SEP M | `□A → A` | reflexive |
| B | `A → □◇A` | symmetric |
| 4 | `□A → □□A` | transitive |
| 5 | `◇A → □◇A` | Euclidean |

`TruthCore/Modal/Kripke.lean` defines formulas, frames, valuations and satisfaction, then proves the frame-condition ⇒ axiom-validity direction for K, D, T, B, 4 and 5.

`TruthCore/Modal/Cube.lean` names the fifteen non-redundant systems represented by combinations of D, T, B, 4 and 5 and proves several important collapses explicitly, including:

- T ⇒ D at the frame level;
- B + 5 ⇒ 4, hence KB5 = KB45 semantically;
- D + B + 4 ⇒ T (seriality, symmetry and transitivity give reflexivity);
- S5 ⇒ S4, KTB, KB5 and KD45.

`TruthCore/Modal/Examples.lean` supplies the frontend's default three-world S4 frame. The accessibility relation is the order `actual ≤ nearby ≤ remote`; `p` is true only at `remote`. Lean proves:

- the frame is reflexive and transitive;
- the frame is not symmetric;
- at `actual`, `◇p` but not `□p`;
- at `remote`, `□p`.

## Frontend

The route-only code lives with the route in `apps/corpus-explorer/src/app/modal/`. `/modal` contains two linked views:

- a bird's-eye modal-cube graph of the fifteen systems;
- a possible-world graph whose current world can be changed interactively.

Selecting a modal system closes its axiom set under the semantic implications represented by the MVP and constructs a small finite witness frame satisfying the required conditions. The UI also reports conditions that the concrete witness happens to satisfy beyond those required by the selected logic.

Every graph has a keyboard-operable, structured equivalent: a list of system buttons (with each system's immediate extensions) for the cube, and viewpoint buttons plus an accessibility table for the world graph. The selected system, viewpoint world and valuation are encoded in the URL (`?system=KB5&world=nearby&p=actual`), so a view can be linked and survives reloads; defaults are omitted.

The valuation of `p` can be changed independently. This is important: frame structure controls modal accessibility, while the valuation controls which atomic propositions are true in which worlds.

## Verification boundary

A green Lean build establishes the theorems stated in the modal modules. The React code evaluates its finite graph directly and carries theorem names as explanatory provenance; it is not itself a proof assistant and must not display a stronger claim than the Lean declarations support.

The original Kripke module proves the **frame-condition ⇒ modal-axiom validity** direction for the listed schemes. The path-based `Convergence` module additionally provides a parameterized frame/valuation correspondence and named converse results for 4/B/5. Three obligations must remain distinct: (1) that direction, (2) the converse from validity under every valuation to the frame condition, and (3) soundness/completeness of a syntactic proof system for a frame class. The cube is a semantic frame inventory, not a Hilbert calculus with a proved adequacy theorem. The generic convergence theorem and specialized collapse characterizations do not supply a Hilbert completeness theorem.

It also does **not** establish any of the following:

- that possible worlds are metaphysically real;
- that one modal system is philosophically correct;
- that a natural-language use of “necessary” or “possible” should be modeled by a particular accessibility relation;
- Aristotle's modal syllogistic or medieval Aristotelian/Thomistic modal semantics.

Those are separate philosophical/formalization tasks and should preserve alternative interpretations rather than being smuggled into the Kripke MVP.

## Repository coverage and reuse audit

The table records repository scope as inspected on 28 October 2026. Section
numbers refer to the linked SEP entry; headings organize the audit rather than
asserting that the article's results have been implemented. Existing theorem
bodies, their exact hypotheses and their result gates remain the evidence.

| Topic / SEP sections | Existing repository coverage | Boundary or gap |
| --- | --- | --- |
| Syntax, worlds, frames, axioms and cube (§§1–2, 6–8) | [Kripke](../TruthCore/Modal/Kripke.lean), [Cube](../TruthCore/Modal/Cube.lean), [Examples](../TruthCore/Modal/Examples.lean): K/D/T/B/4/5 validity directions, fifteen frame profiles and selected frame implications. | No general Hilbert derivability relation or full soundness/completeness proof. The named 4/B/5 converse results are supplied by `Convergence`; a full named standard-axiom normalization suite is not claimed. |
| Finite checking and semantic scope (§§6, 12) | [ResearchFinite](../TruthCore/Modal/ResearchFinite.lean) proves `eval_correct` for exhaustively enumerated worlds; [ResearchFixture](../TruthCore/Modal/ResearchFixture.lean) distinguishes all predicates from a fixed expressible language. [K](../TruthCore/Modal/KResearch.lean), [T](../TruthCore/Modal/TResearch.lean), [B](../TruthCore/Modal/BResearch.lean), [S4](../TruthCore/Modal/S4Research.lean), [S5](../TruthCore/Modal/S5Research.lean) and [D](../TruthCore/Modal/DResearch/Language.lean) supply scope laws and controls. | Finite evaluation is not a decision procedure for validity over every frame, nor a complexity/completeness theorem. A limited-language equivalence does not imply world identity. |
| General path-length schema (§9; extra conditions in §8) | [Convergence](../TruthCore/Modal/Convergence.lean) and its [proofs](../TruthCore/Results/Modal/Convergence/Solution.lean) connect exact-length Quiver paths to iterated modalities, prove fork/join convergence iff one-atom schema validity under every valuation, and specialize 4/B/5. [Certificate](../TruthCore/Modal/ConvergenceCertificate.lean) assembles the stated results. | This is frame/valuation correspondence, not Hilbert completeness. Length zero means identity; arbitrary finite reachability is a different relation. Named reductions beyond the stated specializations are not claimed. Analytic [time convergence](../TruthCore/Causality/ConvergentSchedule.lean) remains a different notion. |
| Quantification and domains (§16) | [GoedelGod](../TruthCore/Isabelle/AFP/GoedelGod.lean) provides shallow `Box`/`Dia` with constant-domain individuals and higher-order properties. [HOML1](../TruthCore/Isabelle/AFP/NotesOnGoedel/GoedelVariantHOML1.lean) adds existence-guarded individual quantification. [Ontic](../TruthCore/German/Kant/CosmologicalInference.lean) and [NecessaryIndividual/Quantifiers](../TruthCore/Case/Catholicism/StageOne/NecessaryIndividual/Quantifiers.lean) separate rigid candidate identity, presence, de re/de dicto and joint absence. | These are supplied semantic embeddings and particular consequences. No general quantified syntax with substitution/assignment metatheory, Barcan/converse-Barcan domain characterization, non-rigid-term semantics, or free-logic proof calculus found. Existence guards alone do not certify such a calculus. |
| Bisimulation and correspondence theory (§§13–14) | Fixed-language controls above already test what formulas distinguish. | No generic bisimulation relation/truth-preservation theorem, standard-translation metatheory, Sahlqvist theorem or van Benthem characterization found. Specialized equal-truth models are not those general theorems. |
| Domain-specific operators (§§3–5, 10–11, 15) | [TruthPilot](../TruthCore/Logic/TruthPilot.lean) treats limited knowledge; [McTaggart](../TruthCore/Comparison/McTaggart.lean) treats a time argument; [PlanStateEmbedding](../TruthCore/Metaethics/PlanStateEmbedding.lean) treats norm/plan predicates. These are distinct local vocabularies. | No general deontic, tense, conditional/relevance, two-dimensional/indexical, GL/arithmetic-provability, dynamic/multi-agent or game-modal engine found. The local arguments are not implementations of those systems; Gödel's ontological-argument embedding is not provability logic. |
| Current metaphysical consumers | [ExistenceDegrees](../TruthCore/Modal/ExistenceDegrees.lean), [ExistenceDegreeAttainment](../TruthCore/Modal/ExistenceDegreeAttainment.lean), [NecessaryVariableEffects](../TruthCore/Modal/NecessaryVariableEffects.lean), [PowerExistenceBoundary](../TruthCore/Causality/PowerExistenceBoundary.lean) reuse the shared frame/Ontic semantics while retaining distinct degree, activity, power and existential-support predicates. | Conditional consequences do not validate those metaphysical bridges or identify the relations. No root premise closes through a change of notation. |
| Graph interoperability | [GraphBridge](../TruthCore/Modal/GraphBridge.lean) supplies explicit directed Digraph/Quiver adapters; its [proofs](../TruthCore/Results/Modal/GraphBridge/Solution.lean) cover round trips, reachability/closure, S4 access agreement, K4 boxed persistence and K45 successor cones. [Certificate](../TruthCore/Modal/GraphBridgeCertificate.lean) and its canonical result retain all original helper signatures as comparison targets. | Edges keep direction and self-loops; no global Quiver instance is installed on a world type. A Unit dead-end control separates nil paths from edges and demonstrates that replacing access by closure changes boxed truth. These adapters do not identify accessibility with causation or establish world identity. |

## Standard-system inventory and bounded T/D extension

The shared interface remains `Frame`, `Formula`, `Holds` and `Valid` in
`Modal.Kripke`. Its `axiomK_valid`, `axiomT_valid`, `axiomD_valid`,
`axiomB_valid`, `axiom4_valid` and `axiom5_valid` prove forward validity.
`Modal.Cube` already records fifteen frame profiles, `kt_implies_kd`, and
`s5_implies_s4`, `s5_implies_ktb`, `s5_implies_kb5`, `s5_implies_kd45`.
`Results.Modal.Convergence` supplies the generic exact-path correspondence
and named 4/B/5 instances. These existing results are reused, not re-proved.

The bounded extension in
[StandardCorrespondence](../TruthCore/Results/Modal/StandardCorrespondence/Solution.lean)
adds only `t_iff_reflexive` and `d_iff_serial`. Each uses the single atom `()`
but validity still quantifies over **every** valuation and world. The T converse
selects the valuation `P(v) = access(w,v)` for each chosen w; its boxed premise
holds by identity and its conclusion yields `access(w,w)`. The D converse
uses the constant-true valuation, so its diamond witness supplies a successor.
The reverse directions reuse `axiomT_valid` and `axiomD_valid`. No inhabitedness,
excluded middle, or frame restriction is an input; with an empty world type,
validity and the corresponding universal frame conditions hold vacuously.

Here symmetry corresponds to the **B axiom**, or the cube node `KB`.
The standard system B includes T as well (`KTB` in this repository); symmetry
alone is not that standard system. Reflexivity makes a necessary proposition
true at the standpoint; seriality only supplies a successor. Neither condition
is a statement about world-local causes, concrete existence or temporal past.
This fills the named T/D correspondence gap without constructing a Hilbert
calculus, claiming completeness, or discharging any philosophical premise.

## Prioritized next uses

1. Consume the graph adapter and exact-path correspondence in
   the existing frame experiments. Preserve the distinction between an edge and
   a zero-or-more-edge path; do not add frame assumptions to obtain a round trip.
2. Reuse the existing shared frame and Ontic interfaces for promising
   metaphysical consequences. Extract the duplicated local degree-dominance
   lemma only when it helps its two existing consumers (named global maximality
   and the attainment equivalence); keep their frozen Challenges unchanged.
3. If a live argument needs movement between domain policies, add one explicit
   Barcan/domain bridge with omission controls using the existing guarded and
   constant-domain embeddings. Do not infer persistence of existence from a
   rigid roster. If a live model comparison needs language preservation, prefer
   a small bisimulation-invariance lemma over a new modal engine.
4. Add characteristic-valuation converse proofs when a consumer needs frame
   reconstruction. Full Hilbert soundness/completeness and further domain-specific systems
   remain deferred without such a consumer; the exact-path family above is available
   for further justified specializations.

This inventory introduces no dependency, source-attributed claim, philosophical
premise or root-frontier change. It replaces the older suggestion to build a
finite checker from scratch: a checked finite evaluator already exists.
