# Modal logic MVP

This slice adds a small, mechanically checked laboratory for normal propositional modal logic without changing the source-corpus model.

## Purpose

The MVP should make three different things visible without conflating them:

1. **Modal syntax** — propositions can be qualified by necessity (`□`) and possibility (`◇`).
2. **Kripke semantics** — truth is evaluated at a world relative to an accessibility relation and an atomic valuation.
3. **Frame restrictions** — adding modal axioms restricts the admissible accessibility relations, producing the familiar modal cube.

The frontend is an explorable model of those semantics. Lean is the verification boundary for the generic correspondence direction implemented here and for the concrete S4 example.

## Reference and evidence boundary

This slice is mathematics, not a source-derived corpus claim. It creates no `corpus/` statement, claim, passage, or argument record, and nothing in it is attributed to a source. The frame-condition ⇒ axiom-validity direction of the correspondences below is established by the Lean proofs in `TruthCore/Modal/` (the converse is not yet formalized), not by citation, so the AGENTS.md source-materialization invariants for source-derived claims do not apply.

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

This MVP proves the **frame-condition ⇒ modal-axiom validity** direction for the listed schemes. Three obligations must remain distinct: (1) that direction, (2) the converse from validity under every valuation to the frame condition, and (3) soundness/completeness of a syntactic proof system for a frame class. The cube is a semantic frame inventory, not a Hilbert calculus with a proved adequacy theorem. Specialized collapse characterizations elsewhere do not supply the missing general converse or completeness results.

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
| Syntax, worlds, frames, axioms and cube (§§1–2, 6–8) | [Kripke](../TruthCore/Modal/Kripke.lean), [Cube](../TruthCore/Modal/Cube.lean), [Examples](../TruthCore/Modal/Examples.lean): K/D/T/B/4/5 validity directions, fifteen frame profiles and selected frame implications. | No general Hilbert derivability relation, full soundness/completeness proof, or full standard-axiom converse correspondence suite found. |
| Finite checking and semantic scope (§§6, 12) | [ResearchFinite](../TruthCore/Modal/ResearchFinite.lean) proves `eval_correct` for exhaustively enumerated worlds; [ResearchFixture](../TruthCore/Modal/ResearchFixture.lean) distinguishes all predicates from a fixed expressible language. [K](../TruthCore/Modal/KResearch.lean), [T](../TruthCore/Modal/TResearch.lean), [B](../TruthCore/Modal/BResearch.lean), [S4](../TruthCore/Modal/S4Research.lean), [S5](../TruthCore/Modal/S5Research.lean) and [D](../TruthCore/Modal/DResearch/Language.lean) supply scope laws and controls. | Finite evaluation is not a decision procedure for validity over every frame, nor a complexity/completeness theorem. A limited-language equivalence does not imply world identity. |
| General h/i/j/k axiom and convergence (§9; extra conditions in §8) | Existing frame implications can be reused from `Kripke`/`Cube`. | No general relational-power convergence theorem, or dedicated functional/shift-reflexive/dense/convergent frame correspondence suite found. [ConvergentSchedule](../TruthCore/Causality/ConvergentSchedule.lean) concerns analytic convergence of times, a different notion. |
| Quantification and domains (§16) | [GoedelGod](../TruthCore/Isabelle/AFP/GoedelGod.lean) provides shallow `Box`/`Dia` with constant-domain individuals and higher-order properties. [HOML1](../TruthCore/Isabelle/AFP/NotesOnGoedel/GoedelVariantHOML1.lean) adds existence-guarded individual quantification. [Ontic](../TruthCore/German/Kant/CosmologicalInference.lean) and [NecessaryIndividual/Quantifiers](../TruthCore/Case/Catholicism/StageOne/NecessaryIndividual/Quantifiers.lean) separate rigid candidate identity, presence, de re/de dicto and joint absence. | These are supplied semantic embeddings and particular consequences. No general quantified syntax with substitution/assignment metatheory, Barcan/converse-Barcan domain characterization, non-rigid-term semantics, or free-logic proof calculus found. Existence guards alone do not certify such a calculus. |
| Bisimulation and correspondence theory (§§13–14) | Fixed-language controls above already test what formulas distinguish. | No generic bisimulation relation/truth-preservation theorem, standard-translation metatheory, Sahlqvist theorem or van Benthem characterization found. Specialized equal-truth models are not those general theorems. |
| Domain-specific operators (§§3–5, 10–11, 15) | [TruthPilot](../TruthCore/Logic/TruthPilot.lean) treats limited knowledge; [McTaggart](../TruthCore/Comparison/McTaggart.lean) treats a time argument; [PlanStateEmbedding](../TruthCore/Metaethics/PlanStateEmbedding.lean) treats norm/plan predicates. These are distinct local vocabularies. | No general deontic, tense, conditional/relevance, two-dimensional/indexical, GL/arithmetic-provability, dynamic/multi-agent or game-modal engine found. The local arguments are not implementations of those systems; Gödel's ontological-argument embedding is not provability logic. |
| Current metaphysical consumers | [ExistenceDegrees](../TruthCore/Modal/ExistenceDegrees.lean), [ExistenceDegreeAttainment](../TruthCore/Modal/ExistenceDegreeAttainment.lean), [NecessaryVariableEffects](../TruthCore/Modal/NecessaryVariableEffects.lean), [PowerExistenceBoundary](../TruthCore/Causality/PowerExistenceBoundary.lean) reuse the shared frame/Ontic semantics while retaining distinct degree, activity, power and existential-support predicates. | Conditional consequences do not validate those metaphysical bridges or identify the relations. No root premise closes through a change of notation. |
| Graph interoperability — **IN PROGRESS** | A faithful `Frame` → Mathlib Digraph/Quiver adapter is being investigated on `sprint/20261028-kripke-graph`; module name pending. Follow the current handoff in [#418](https://github.com/moritzbrantner/truth-core/issues/418). | Planned obligations: adjacency/access round trip; Quiver reachability versus reflexive-transitive closure; S4 reachability/access agreement; transitive box persistence; K45 successor-cone agreement; a dead-end control separating a zero-edge path from one-step access. None is advertised as verified here. This is separate from the motion respect-label constraint. |

## Prioritized next uses

1. Finish the bounded graph adapter and its dead-end control, then consume it in
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
   reconstruction. Full Hilbert soundness/completeness, general h/i/j/k coverage,
   and further domain-specific systems remain deferred without such a consumer.

This inventory introduces no dependency, source-attributed claim, philosophical
premise or root-frontier change. It replaces the older suggestion to build a
finite checker from scratch: a checked finite evaluator already exists.
