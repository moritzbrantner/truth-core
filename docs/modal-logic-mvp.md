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

The Stanford Encyclopedia of Philosophy entry “Modal Logic” (sections 7–8, https://plato.stanford.edu/entries/logic-modal/) was used only for orientation on standard terminology and the shape of the modal cube, as AGENTS.md permits for catalogs and secondary literature. If a later slice attributes a modal thesis to a source (for example Aristotle's modal syllogistic), that slice must add a pinned `corpus/passages/` witness and follow the ordinary atomic loop.

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

This MVP proves the **frame-condition ⇒ modal-axiom validity** direction. It does not yet formalize the full converse correspondence/completeness results for every system in the cube.

It also does **not** establish any of the following:

- that possible worlds are metaphysically real;
- that one modal system is philosophically correct;
- that a natural-language use of “necessary” or “possible” should be modeled by a particular accessibility relation;
- Aristotle's modal syllogistic or medieval Aristotelian/Thomistic modal semantics.

Those are separate philosophical/formalization tasks and should preserve alternative interpretations rather than being smuggled into the Kripke MVP.

## Natural next slices

1. Prove the converse correspondence direction for D/T/B/4/5 using characteristic valuations.
2. Add a tiny formula parser and model checker whose examples can be cross-checked against Lean fixtures.
3. Export proof-backed example fixtures instead of manually mirroring them in TypeScript.
4. Add countermodel mode: when an axiom is not implied, show a frame falsifying it.
5. Only after the Kripke layer is stable, add a separate Aristotelian modal-semantics namespace and compare interpretations rather than treating them as interchangeable.
