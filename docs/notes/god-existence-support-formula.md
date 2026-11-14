# Exact support formula for God-existence (2026-11-13)

Corpus snapshot: `960fe26728cee3f3467950d3aab67ded6cf2eb39`. This note answers which combinations of the corpus's recorded propositions suffice through its registered argument graph. It is a research reference, not another queue or a change to premise status.

## Targets

- **G:** `STMT-GOD-EXISTS` (`8626f8a5-9531-5da7-9ebd-f901e74b1129`), whose Lean body is `∃ g, IsGod g`, instantiated at the case signature's GOD_4 predicate.
- **H:** `STMT-NECESSARY-CLASSICAL-GOD-ROOT` (`da3facd6-008e-5e76-92fa-677350c2dfdb`), retaining one and the same actual concrete necessary root and the exact nine case attribute predicates.

The corpus has a registered projection H → G. GOD_4 is a primitive predicate constrained by explicit naming and attribute premises; its name does not definitionally supply the attributes. The calculation retains every such bridge. See [the target definition](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/TruthCore/Case/Catholicism/Root.lean) and [the stronger same-witness definition](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/TruthCore/Causality/NecessaryClassicalGodRoot.lean). The stronger target retains the encoded senses of goodness, intellect and will; it does not silently strengthen them to moral omniperfection, omniscience or free will.

## Immediate disjunction: exact result

There are **13 registered immediate arguments**, using **33 distinct statement inputs**. Their direct sufficient condition is the disjunction of their 13 premise conjunctions. Ordinary absorption (`A ∨ (A ∧ B) = A`) leaves **9 irredundant direct conjunctions**:

$$\Phi_G^{\mathrm{direct}}=C_{01}\lor C_{02}\lor C_{03}\lor C_{04}\lor C_{05}\lor C_{06}\lor C_{07}\lor C_{10}\lor C_{11}. $$

In the next table, a list of numbers means the conjunction of those P inputs; for example `02, 12` means `P02 ∧ P12`. Symbols are local notation, not new corpus identities.

| Clause | Conjuncts | Registered argument | Direct absorption |
| --- | --- | --- | --- |
| C01 | 24 | [92ab7c94](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/92ab7c94-80b1-4d05-bcaa-e59394ea55b2.json) | Retained |
| C02 | 02, 12, 13, 14, 30 | [ed7c588a](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/CATHOLICISM-STAGE1-FROM-PRIMA-VIA.json) | Retained |
| C03 | 01, 03, 10, 15, 19, 20, 26, 33 | [5d2b7c6e](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/5d2b7c6e-57b3-44c1-ac3a-9789b65c63fb.json) | Retained |
| C04 | 01, 03, 05, 10, 15, 19, 20, 26 | [678ff65f](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/god-exists-from-maxime-ens-causing-all.json) | Retained |
| C05 | 01, 03, 05, 10, 15, 17, 20, 21, 22, 26, 29 | [661ce61d](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/CATHOLICISM-STAGE1-FULL-DESCRIPTION-WITHOUT-MOTION.json) | Retained |
| C06 | 01, 06, 07, 10, 11, 15, 18, 21, 26, 28, 31, 32 | [3367bf93](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/3367bf93-3e4c-43c0-b31b-06375e7c4685.json) | Retained |
| C07 | 01, 06, 07, 10, 11, 15, 17, 21, 26, 28, 31, 32 | [5e8e6054](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/direct-esse-root-god-existence-only.json) | Retained |
| C08 | 01, 06, 07, 08, 10, 11, 15, 17, 21, 26, 28, 31, 32 | [72391d4d](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/direct-esse-root-god-existence.json) | C07 |
| C09 | 01, 06, 07, 08, 10, 11, 15, 18, 21, 26, 28, 31, 32 | [fc46b7f9](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/fc46b7f9-32d0-416d-8f72-5bc908992f30.json) | C06 |
| C10 | 01, 04, 06, 08, 10, 15, 17, 21, 23, 25, 26, 28, 31, 32 | [1c154f2f](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/necessary-root-god-existence-reduced.json) | Retained |
| C11 | 01, 05, 09, 10, 12, 13, 14, 16, 17, 21, 22, 27, 29, 30 | [beec1dc1](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/CATHOLICISM-STAGE1-VIA-MAXIME-ENS.json) | Retained |
| C12 | 01, 03, 05, 09, 10, 12, 13, 15, 17, 20, 21, 22, 26, 27, 29 | [fd1f7e75](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/CATHOLICISM-STAGE1-VIA-FULL-DESCRIPTION.json) | C05 |
| C13 | 01, 04, 06, 08, 10, 15, 17, 21, 22, 23, 25, 26, 28, 29, 31, 32 | [0a639ec4](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/arguments/necessary-root-god-existence.json) | C10 |

C08 is absorbed by C07; C09 by C06; C12 by C05; C13 by C10. These nine clauses are irredundant by literal premise-set absorption; registered implications between distinct inputs can permit further simplification. This is simplification of the sufficient-condition formula, not deletion or devaluation of any argument. A stronger route may retain a richer intermediate result. C01 is direct acceptance of H followed by projection: it stays available, while H's seven registered derivations are expanded in the full calculation.

### Input dictionary

These are concise readings for navigation. Each link resolves the precise proposition, definition/sense links and Lean declaration; the machine-readable snapshot preserves the complete canonical paraphrases.

| Symbol | Statement |
| --- | --- |
| P01 | [Actuality in any respect entails having being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/actuality-only-insofar-as-being.json) (`7067553d-cad9-5d79-b6b2-912e35051530`) |
| P02 | [At most one first unmoved mover exists.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/at-most-one-first-unmoved-mover.json) (`c27dce66-864a-5a73-af62-0eeb4016514f`) |
| P03 | [A cause of a thing's being causes each of its actual perfections.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/cause-of-being-causes-every-perfection.json) (`f8ba2429-b4f1-5712-a4d3-798213963d34`) |
| P04 | [Causing a necessary being's being entails causing its necessity.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/cause-of-necessary-being-causes-its-necessity.json) (`3c468121-b8fe-5342-a1ab-d35009e5fdd4`) |
| P05 | [A cause of a quality in another is more such than that other.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/cause-of-quality-in-another-is-more-such.json) (`d5a94eb1-72d2-53e0-9a52-9787b5b61a8d`) |
| P06 | [Some actual concrete individual exists at the selected world.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/cogito-inhabited-concrete-world.json) (`56f68b40-9737-59a0-8cac-5610980a1547`) |
| P07 | [A distinct esse cause of an actual concretum is its actual concrete ground.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/esse-cause-is-actual-concrete-ground.json) (`cb1cdea9-eb6c-578c-8008-84e0d4107fd3`) |
| P08 | [Every actual contingent concretum has an actual concrete ground.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/every-contingent-grounded-at.json) (`c71c068c-bbae-5ed5-a99d-70b155c8d239`) |
| P09 | [Every created agent is itself moved whenever it moves something, under the recorded application reading.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/every-created-agent-acts-as-applied-to-act-by-god.json) (`777646a5-3f40-5508-b59a-5e019cf2edce`) |
| P10 | [Excluded middle for every proposition.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/excluded-middle.json) (`ee4ab504-c8fe-59bc-bc96-7cbeefed6410`) |
| P11 | [Selected-world represented existence entails actuality in the supplied esse respect.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/existing-in-act-at.json) (`0436de86-6579-53f2-9ff5-2111ba44ebae`) |
| P12 | [There cannot be no first unmoved mover (the recorded double-negation premise).](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/first-unmoved-mover-cannot-be-lacking.json) (`c1b68c21-fa36-5ab0-a499-444259eda78a`) |
| P13 | [Either a first unmoved mover exists or none exists.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/first-unmoved-mover-exists-or-not.json) (`ca075552-10fc-5d18-afb8-f0344bdcf77c`) |
| P14 | [Every first unmoved mover is pure act.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/first-unmoved-mover-is-pure-act.json) (`6c18d52b-2456-59ae-995f-13440f8c808d`) |
| P15 | [The full nominal profile suffices for the GOD_4 name, under the recorded component-remoteness reading.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/god-names-the-fully-described-principle.json) (`1ec205ed-b2a6-5384-bb5f-2565a9d325bf`) |
| P16 | [The reduced unique-maximum/causal profile suffices for the God name.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/god-names-the-unique-maxime-ens.json) (`e39a4fce-ccaf-5862-836e-9317923842f3`) |
| P17 | [Grades in any perfection imply a maximum in that perfection.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/grades-have-a-maximum.json) (`6c27657f-a2bf-5c1d-963c-c154b66bfa85`) |
| P18 | [Comparison in esse implies an in-act maximum in esse.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/grades-to-maximum-at-being.json) (`e4e6b0cd-f61a-5605-a302-573c67cf063a`) |
| P19 | [A maximum in being exists and causes the being of every other being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/maxime-ens-causes-being-of-all.json) (`0881e859-c4c3-53ff-9bec-b61294e12d51`) |
| P20 | [Every maximum in being is a first being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/maximum-in-being-is-first-being.json) (`eaa4c679-98a3-5e82-95ff-18bd1177ce74`) |
| P21 | [A maximum in a genus causes that perfection in all others having it.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/maximum-in-genus-causes-all-in-genus.json) (`d9fad785-40ab-555a-a1c1-5e39c9d50497`) |
| P22 | [Every maximum in truth is a maximum in being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/most-true-is-most-being.json) (`101bdd62-7cd0-5923-8f03-d9d443f4ba51`) |
| P23 | [A necessary being is in act as to being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/necessary-being-has-being.json) (`79281639-e09b-569c-a2b3-bb32fdc3b951`) |
| P24 | [H: one same necessary classical God-root with the recorded nine attributes.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/necessary-classical-god-root.json) (`da3facd6-008e-5e76-92fa-677350c2dfdb`) |
| P25 | [A distinct cause of necessity is an actual concrete ground at the selected world.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/necessity-causes-actual-concrete-grounds.json) (`d29cebca-ee1c-5bd8-9080-f7226770e809`) |
| P26 | [No component of anything is a first being.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/no-component-is-first-being.json) (`09c6d5f0-d412-5038-85f9-75fffb935727`) |
| P27 | [Moving another in a respect requires being in act in that respect.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/nothing-moves-except-as-in-act.json) (`f296a694-aeea-5fa7-bdbf-0076530f9441`) |
| P28 | [A distinct simply-prior individual is an actual concrete ground at the selected world.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/simply-prior-is-actual-concrete-ground.json) (`86efed1a-f353-5b5d-9431-df7fc643ace1`) |
| P29 | [There are grades of goodness, truth and nobility.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/things-more-and-less-good-true-noble.json) (`a9622441-2db2-5d32-9b02-a9d283bd2949`) |
| P30 | [A unique pure-act first unmoved mover is GOD_4.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/unique-pure-act-first-mover-is-god.json) (`a594d8c4-8d2e-5de3-b719-f1a8ee3b7b96`) |
| P31 | [A universal cause of being transfers a distinct effect's esse causation to its actual perfections.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/universal-cause-transfers-perfections.json) (`b26c10a0-983d-5a88-aa03-cc601bc1ddc6`) |
| P32 | [The nonempty whole actual concrete roster is not a borrowing trap under the selected graph-source reading.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/whole-roster-not-trapped.json) (`5c898d24-d1f7-5087-b09e-3287a723e787`) |
| P33 | [A distinct cause of a thing's being is more in being than that thing.](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/cffad050-e86d-48b8-b04b-be47fcc1352d.json) (`cffad050-e86d-48b8-b04b-be47fcc1352d`) |

## Full recursive support formula

The backward slice has **600 statement nodes and 445 registered argument/result rules**. For G, the direct-input basis contains the other **599** statements. Source `supports`, `attacks` and lexical similarity are not implication rules. Registered transcriptions and strength implications are included as conditional logical edges, with their provenance retained. Neither `closed` nor `established` metadata is inserted as a premise-free theorem.

Let x_p mean that p is supplied directly as a premise. False means it is not supplied; it does not mean that p is false. Exclude the requested target from the supplied inputs. For every statement p, compute the least fixed point:

$$F_p=x_p\lor\bigvee_{r:\operatorname{conclusion}(r)=p}\ \bigwedge_{q\in\operatorname{premises}(r)}F_q.$$

An actual zero-premise rule contributes true. An empty list of derivations contributes false. This treatment permits cycles in the graph while preventing a cycle from supplying its own initial evidence. Direct acceptance and derivation remain alternatives: if A ∧ B → P, the available support for P includes `x_P ∨ (F_A ∧ F_B)`.

The requested DNF is:

$$\Phi_G=\bigvee_{S\in\mathcal M_G}\ \bigwedge_{p\in S}x_p,$$

where M_G is the family of inclusion-minimal input sets whose forward closure contains G. Shared premises occur once in a conjunction. Several proof paths may witness the same conjunction; they do not become independent evidence merely by being counted separately.

A second projection sets every direct input for a statement with an incoming registered rule to false. This **terminal-input calculation** expands those statements instead of taking them directly. It answers a different question and supplements the direct-or-derived view; it does not replace it. Ungrounded cycles then contribute nothing without a terminal entry.

## Exactness and proof boundary

The equivalence proved by this computation is between the support formula and **derivability in the fixed registered statement-ID graph**. Under the recorded theorem interpretations it is a sufficient condition for the target. It is not a claim that every possible argument for God is already in the corpus, nor that absence of a current support proves nonexistence.

Twelve direct G routes end in `GodExists IsGod` with an explicitly supplied predicate and naming/identification premises; the H projection ends in `GodExists σ.IsGod`. They can be specialized at the same GOD_4 signature. A fresh jointly elaborated Lean composition still has to match all carriers, world/model parameters, respect constants and interpretations. The dependency calculation does not replace that binding/Comparator/NanoDa boundary or certify joint satisfiability of every premise package.

The existing Rust `truth frontier --routes` is a useful greedy diagnostic: it selects one leaf set per statement. It does not enumerate the exact DNF. The existing configuration antichain helper is exact when it reaches a fixed point without truncation; its default 128-combination bound and the territory 20,000-combination bound both truncate this slice. No bounded partial count is presented here as the full answer.

## How to use this as the work target

1. Select G or H explicitly; use H when the task concerns the retained necessity and attributes of the same witness.
2. Select a concrete conjunction and investigate one named input, a bridge that replaces it, or a substantive objection to it. Keep the direct-acceptance option visible while adding support.
3. Recompute the formula after the corpus changes. Report which alternative conjunctions appeared, which became redundant, and which exact shared obligations changed. Do not use the number of nodes or conjunctions as a warrant score.
4. Reuse the same proposition issue across clauses that consume it. New work should name its target UUID, downstream clause(s), existing support, exact uncertainty and a discriminating next test.
5. Distinguish removing an input option from proving its negation. Hitting every current conjunction blocks these encoded routes; it does not by itself establish atheism.

## Snapshot verification

- Built and ran the current Rust CLI; `truth check` passed on the corpus snapshot.
- The God-target frontier was generated by `target/release/truth frontier --frontier-root STMT-GOD-EXISTS --json`; its corpus input identity is `fnv1a64:3e78843aeae9175f`.
- Read every direct G Solution telescope and the G/H definitions. No new Lean theorem, source attribution, corpus record or closure status was introduced.
- Independent review checked all immediate clauses, dictionary mappings, absorptions and the G/H interpretation boundary. The completed symbolic calculation is described below.

## Complete terminal-input DNF

The terminal basis has **368** statement IDs: every node with no incoming registered rule. All other direct-input variables are set to false. Registered zero-premise rules still run. Both calculations reached their least fixed points; neither report uses a route cap or a truncated enumeration.

| Target | Inclusion-minimal conjunctions | Smallest conjunction | Largest inclusion-minimal conjunction | Inputs shared by every conjunction |
| --- | ---: | ---: | ---: | ---: |
| G: GodExists | 67,798,928 | 39 | 149 | 9 |
| H: same necessary classical God-root | 109,971,456 | 100 | 149 | 75 |

$$\Phi_G^T=\bigvee_{S\in\mathcal M_G^T}\ \bigwedge_{p\in S}x_p,\qquad |\mathcal M_G^T|=67{,}798{,}928.$$

There are **18** G conjunctions of the minimum size, 39. These are premise-package counts, not counts of independent arguments or evidence weights. The terminal expansion deliberately removes direct acceptance of intermediate claims; the direct-or-derived equation system above preserves that option. The larger number for H is compatible with H implying G: G's other sufficient subsets can absorb many H packages.

The complete family is stored as an exact reduced ordered binary decision diagram in `god-bdd-terminal-exact.json` (2,412,015 bytes for both target formulas and both minimal-support families). The file specifies its variable order, node and complemented-edge semantics and named roots. A satisfying assignment of a `_minimal` root names exactly one conjunction: take precisely the statement inputs assigned true. The full graph/dictionary and report supply the UUID mapping and provenance. Thus every conjunction is recoverable without printing tens of millions of overlapping lines.

The all-input formula is retained exactly by the 600-node/445-rule least-fixed-point system in `god-existence-support-graph.json`. A flat all-input DNF count is not claimed. The completed numerical table above concerns the explicitly defined terminal basis.

### Nine shared terminal obligations for G

The [nine-premise support investigation](nine-premise-support-investigation.md)
records additional arguments, source support and explicit bridge proposals for
each of these inputs, with the remaining application conditions distinguished
from formal consequence.

Each following input occurs in every G conjunction **under this terminal-only expansion**. Removing its supplied input makes this expanded formula false. This does not say the proposition is false, universally indispensable to theism, or unavoidable when intermediate claims may be accepted directly.

| Statement | Exact recorded premise |
| --- | --- |
| [STMT-DEPENDENCE-EXCLUDES-BEING-WITHOUT](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/dependence-excludes-being-without.json) | OPEN analyst premise: if x depends for its being on y, then x cannot be without y. It reads the counterfactual dependence of DEF-DEPENDS-FOR-BEING as excluding the real possibility of x's being while y is not. |
| [STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/distinct-beings-not-mutually-dependent.json) | OPEN analyst premise: no two distinct things depend for their being on each other; if x is distinct from y and x depends for its being on y, then y does not depend for its being on x. Restricted to distinct things because DependsForBeing, read counterfactually, holds trivially of a thing and itself. Navigation only (no claim): Aquinas, In V Metaph. lect. 13 n. 18, 'priora non dependent a posterioribus, sicut e converso'. |
| [STMT-POTENCY-IS-CAPACITY-UNDER-PRIVATION](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/potency-is-capacity-under-privation.json) | OPEN analyst premise: to be in potency to r is to be capable of r and deprived of r: ∀ x r, InPotency x r ↔ CanBe x r ∧ Deprived x r. The subject-privation pair of Physics I.7-8 applied to capacities; the identification is the analyst's. |
| [STMT-PRIORITY-REQUIRES-NONMUTUAL-DEPENDENCE](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/priority-requires-nonmutual-dependence.json) | OPEN analyst premise (the other direction): if y is simply prior to x, then x depends for its being on y and y does not so depend on x. |
| [STMT-PRIVATION-IS-LACK-OF-ACT-IN-CAPABLE](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/privation-is-lack-of-act-in-capable.json) | OPEN analyst premise: in a subject capable of r, privation of r is exactly the lack of r in act: ∀ x r, CanBe x r → (Deprived x r ↔ ¬ InAct x r). It says nothing about incapable subjects (a mere negation is no privation). |
| [STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/independence-allows-being-without.json) | OPEN analyst premise: if y does not depend for its being on x, then y can be without x. It fails when x's not being is itself impossible, since then y cannot be while x is not although y does not depend on x. |
| [STMT-PRIORITY-BY-BEING-WITHOUT](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/priority-by-being-without.json) | OPEN analyst reading of the criterion of natural priority: if y can be without x and x cannot be without y, then y is simply prior to x. Navigation only (no claim): Aquinas, In V Metaph. lect. 13 n. 15, 'priora dicuntur, quae possunt esse sine aliis et illa non possunt esse sine eis', said of priority 'secundum naturam'; reading it for the simple priority of DEF-SIMPLE-PRIORITY is the analyst's. |
| [STMT-EFFECT-DEPENDS-FOR-BEING-ON-EFFICIENT-CAUSE](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/effect-depends-for-being-on-efficient-cause.json) | OPEN reading of ST I q.44 a.1 ad 2 as dependence: whatever c efficiently causes in any respect depends for its being on c (it would not be if c were not). |
| [STMT-EXCLUDED-MIDDLE](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/excluded-middle.json) | Excluded middle as a general principle: every proposition either holds or does not hold (∀ p, p ∨ ¬p). |

These cluster into the meaning of potency/privation, the relationship between efficient causation and existential dependence, the relationship between priority and nonmutual dependence/being-without, and excluded middle. A focused issue can investigate a named bridge or add an alternative sufficient derivation and then measure exactly which conjunctions it changes. In particular, the record for independence allowing being-without already identifies the necessary-existence qualification; inspect that precise scope rather than inventing a generic objection.

### One complete 39-input conjunction

The following is one of the 18 smallest terminal conjunctions. All 39 premises are jointly required for this displayed graph-minimal package; they are not ranked by plausibility. Forward chaining derives G from this set, and deleting any single member prevents G from being derived from the remainder in this graph. A replay trace is included in the calculation report. Each exact statement is linked below; its full paraphrase and Lean declaration are in the machine-readable dictionary.

| No. | Statement |
| --- | --- |
| 1 | [000e1f65-6e74-5519-bbf3-300d5f61ada8](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/dependence-excludes-being-without.json) — OPEN analyst premise: if x depends for its being on y, then x cannot be without y. It reads the counterfactual dependence of DEF-DEPENDS-FOR-BEING as excluding the real possibility of x's being while y is not. |
| 2 | [0a7896e7-fc8a-55b2-a368-978bda235b31](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/aquinas-active-power-only-in-act.json) — At the selected world, whatever has causal power, an active power or principle of acting on another, is in act in some respect: each thing is an active principle insofar as it is in act. Neither the converse nor any degree of power is included. |
| 3 | [0f49d71e-09e6-5a9c-b7e7-e0e9b8fe769c](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/distinct-beings-not-mutually-dependent.json) — OPEN analyst premise: no two distinct things depend for their being on each other; if x is distinct from y and x depends for its being on y, then y does not depend for its being on x. Restricted to distinct things because DependsForBeing, read counterfactually, holds trivially of a thing and itself. Navigation only (no claim): Aquinas, In V Metaph. lect. 13 n. 18, 'priora non dependent a posterioribus, sicut e converso'. |
| 4 | [196e6606-d61b-59c4-a12b-7ce056936b92](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/perfect-only-insofar-as-being.json) — Whatever is perfect in some respect is in act as to being: things are perfect insofar as they have being in some way. Encodes the second clause of ST I q.4 a.2 co. ('secundum hoc enim aliqua perfecta sunt, quod aliquo modo esse habent'), per respect; 'in some way' is read as being in act in the respect of being. |
| 5 | [2068f91c-1eeb-5dbb-a71a-f7b6a12bb495](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/esse-effect-depends-on-its-cause.json) — OPEN analyst premise: if c, distinct from x, causes x's esse, then x depends for its being on c (DependsForBeing x c, the q.44 a.1 ad 2 counterfactual dependence). Said of causes of esse, not of every efficient cause. |
| 6 | [2e248016-f8bf-5d8a-931e-7f9ebbb13e42](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/actual-dependence-is-grounding.json) — OPEN analyst bridge: if an actual concretum x depends for its being on an actual concretum c, then c grounds x under the selected relation at w. One direction only: grounding is not claimed to be dependence, and dependence on absent or abstract things is not constrained. |
| 7 | [2f6b9eff-84a1-5310-9abb-19985f3282c3](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/total-cause-causes-modes-of-being.json) — OPEN analyst premise: a total cause of a thing's being causes each of that thing's modes of being. |
| 8 | [3b2d2d46-baa6-4772-a2db-bb3daeb092fc](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/3b2d2d46-baa6-4772-a2db-bb3daeb092fc.json) — OPEN analyst generic reading: for the independently supplied InPotency relation, every x in potency in r has some y actual in r simply prior to x. No equation with capacity without act is assumed; adopted-potency instances remain separate. |
| 9 | [3c0b7bb3-1526-55a9-b71e-0d5fb3148782](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/potency-is-capacity-under-privation.json) — OPEN analyst premise: to be in potency to r is to be capable of r and deprived of r: ∀ x r, InPotency x r ↔ CanBe x r ∧ Deprived x r. The subject-privation pair of Physics I.7-8 applied to capacities; the identification is the analyst's. |
| 10 | [47aff057-35ef-5418-930b-fef72e1104d2](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/priority-requires-nonmutual-dependence.json) — OPEN analyst premise (the other direction): if y is simply prior to x, then x depends for its being on y and y does not so depend on x. |
| 11 | [49542121-caa6-576e-aa84-3a1546397388](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/described-principle-is-called-god.json) — GOD_3 reading of the naming premise, OPEN analyst premise (attribution deferred): whatever meets the full nominal description is called 'God' by the speech community ('et hoc dicimus Deum', extended from the quarta via's maximal being to the fuller profile). Usage only: it says how the name is applied, not what its bearer is. |
| 12 | [546975ef-0614-5c0a-8f49-fab2cd2a2533](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/act-of-esse-suffices-for-existence-at.json) — OPEN converse of STMT-EXISTING-IN-ACT-AT: whatever is in act of esse exists at the selected world. InAct is not world-indexed, so this reads esse relative to the selected world; the esse-profile specialization (TruthCore.Logic.CogitoEsse) does not assert it. |
| 13 | [57c5ed67-f9fa-55bb-9b3e-3c00643b21e9](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/simple-priority-relates-actual-concreta.json) — OPEN analyst premise: whenever y is simply prior to x, both y and x are concrete and exist at the reading world w. It excludes abstract or absent relata of simple priority. |
| 14 | [5e281daf-e8a5-5995-bc3f-94e142319e28](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/universal-cause-of-being-is-total.json) — OPEN analyst premise: whatever causes the being of every other being is the total cause of the being of each other thing whose being it causes (it causes that thing's whole being, not only its coming to be in a presupposed subject). |
| 15 | [61bd42e5-69fe-53ef-9972-c9f28b2b6d14](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/q3-a4-essential-principles-not-esse-cause.json) — In Aquinas' q.3 a.4 first proof, the essential principles of an actual subject whose esse differs from its essence cannot sufficiently cause that subject's own esse. This concerns efficient self-causation, not every intrinsic or noncausal explanation. |
| 16 | [6d85b363-58ec-5a8a-9e20-58a93d188ea5](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/called-god-is-classical-god.json) — OPEN sense bridge GOD_3 to GOD_4 (attribution deferred): whatever the speech community calls 'God' is the God of classical theism (IsGod). The 'but is it God?' objection to the five ways denies it. |
| 17 | [791fa216-ce40-5e7d-82c5-0bd5fe245446](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/perfections-are-modes-of-being.json) — OPEN Lean-bound reading of ST I q.4 a.2 co. (STMT-ALL-PERFECTIONS-PERTAIN-TO-PERFECTION-OF-BEING, which has no Lean declaration): every perfection a thing has in act is a mode of its being. |
| 18 | [7a63a3fe-a29f-5282-8106-79fedcb10d08](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/actual-grounding-is-simple-priority.json) — OPEN analyst bridge: whenever an actual concretum a grounds an actual concretum b at w, a is simply prior to b. |
| 19 | [7c3da33e-7ead-54f8-aace-ed3cf3a7bb02](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/privation-is-lack-of-act-in-capable.json) — OPEN analyst premise: in a subject capable of r, privation of r is exactly the lack of r in act: ∀ x r, CanBe x r → (Deprived x r ↔ ¬ InAct x r). It says nothing about incapable subjects (a mere negation is no privation). |
| 20 | [7dfa068a-9974-5fcd-ba23-fac4dee2fc70](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/no-infinite-ascent-in-being.json) — OPEN analyst premise: there is no infinite ascent in being, that is, no sequence of beings each more a being than the one before (Lean WellFounded of 'is more in esse than'). Not a finite domain, a total order or a unique top. |
| 21 | [82eeeb3c-b96d-5483-b1ac-f6059ff02211](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/esse-causes-are-concrete.json) — OPEN analyst premise: whatever causes the esse of anything is concrete (concreteness read as causal capacity). An abstract cause of esse would falsify it. |
| 22 | [86f10ec3-3068-5066-8ba1-3c85baeb1a22](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/component-is-potential-or-participated.json) — Every component of anything is in potency in some respect or has its being by participation. Reads the two kinds of component considered in ST I q.3 a.8's third reason (matter, which is in potency; a form that is part of a composite, which is participated) as exhaustive. |
| 23 | [88b2caf5-03c9-5125-a206-3f39aed61fc4](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/bearer-degrees-directed-in-every-genus.json) — OPEN every-respect version of STMT-SELECTED-PERFECTION-BEARERS-ARE-DEGREE-DIRECTED: for every perfection r, any two bearers of r have a bearer of r at a represented degree at least as high as both. |
| 24 | [8ab3d114-d6e2-5f6d-805b-ae901f56d39b](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/independence-allows-being-without.json) — OPEN analyst premise: if y does not depend for its being on x, then y can be without x. It fails when x's not being is itself impossible, since then y cannot be while x is not although y does not depend on x. |
| 25 | [97fa3a0b-eb23-5fb1-9741-c1f09fb72206](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/priority-by-being-without.json) — OPEN analyst reading of the criterion of natural priority: if y can be without x and x cannot be without y, then y is simply prior to x. Navigation only (no claim): Aquinas, In V Metaph. lect. 13 n. 15, 'priora dicuntur, quae possunt esse sine aliis et illa non possunt esse sine eis', said of priority 'secundum naturam'; reading it for the simple priority of DEF-SIMPLE-PRIORITY is the analyst's. |
| 26 | [98755509-18d3-5282-bd66-47202d916266](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/more-in-exceeds-represented-degree.json) — OPEN analyst calibration (one direction, every respect, every pair): if x is more r than y, x's represented degree of r is strictly higher than y's. |
| 27 | [ac72bbfe-a355-5179-9e29-0a6e565eb79e](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/above-null-degree-has-the-perfection.json) — OPEN analyst premise: whatever stands strictly above the null degree of a perfection r has r (what has some heat is hot). |
| 28 | [ae68972c-175a-5e68-86fb-f69fa30e2054](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/every-existent-has-causal-power.json) — OPEN Eleatic principle at the selected world: every existent has causal power (a capacity, not a present exercise). Rejected by Platonists about causally inert abstracta and by epiphenomenalists. |
| 29 | [be639b3f-a4b7-5ec0-a9be-accfd8d42598](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/q3-a4-distinct-esse-cause-dichotomy.json) — Aquinas' first proof in ST I q.3 a.4 considers an actually existing thing with esse distinct from essence and requires either that the essential principles alone sufficiently efficiently cause its esse or that an actually existing, numerically different agent efficiently cause that esse. Whether this causal dichotomy exhausts noncausal or brute theories is an open premise question. |
| 30 | [c0d99549-799c-5a01-9b59-75fe88550b26](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/effect-depends-for-being-on-efficient-cause.json) — OPEN reading of ST I q.44 a.1 ad 2 as dependence: whatever c efficiently causes in any respect depends for its being on c (it would not be if c were not). |
| 31 | [c94b5446-e7e7-5b36-9bed-288959725526](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/some-actual-contingent.json) — OPEN premise, analyst formulation, attribution deferred: on the route's profile, some concrete individual exists at the selected world w and is absent at some world accessible from w (CONTINGENT_1, ContingentAt: accessible non-existence, not empirical change, CONTINGENT_2). It does not say which being is contingent, that the Cogito bearer is, that it is caused, or that every being other than the root is contingent. It implies STMT-COGITO-INHABITED-CONCRETE-WORLD and excludes concrete necessitarianism (STMT-ALL-ACTUAL-CONCRETE-NECESSARY) on the same frame; the converse of that exclusion needs excluded middle. |
| 32 | [ca84f62d-67cb-58a6-bc3e-a631ab46e3d1](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/perfect-insofar-as-in-act.json) — A thing is perfect in a given perfection exactly when it actually has that perfection ('each thing is perfect insofar as it is in act'), read per perfection as a biconditional. It concerns perfection in one respect, not universal perfection. |
| 33 | [cbb068e8-337d-5772-a3f9-10df457ba9fe](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/participated-has-distinct-esse.json) — OPEN analyst bridge (attribution deferred): whatever has being by participation actually exists with esse distinct from its essence. |
| 34 | [d15ded6f-1895-5d2d-b967-a14165c49bda](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/STMT-NOTHING-SELF-EFFICIENTLY-CAUSES-AT-ANY-ADMITTED-TIME.json) — Open framework premise: at every admitted time, nothing efficiently causes itself in any respect. Stronger than the existing selected-time no-self-efficient-cause premise. No assertion is made about events outside the admitted time domain. |
| 35 | [dc619ad6-11f3-5734-b258-3156b976fc31](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/greatest-degree-causes-all-in-every-genus.json) — OPEN every-respect version of STMT-GREATEST-DEGREE-IN-GENUS-CAUSES-ALL-IN-GENUS: for every perfection r, with r's represented degrees deg r, a bearer at the greatest degree of r causes r in every other bearer of r. |
| 36 | [e433b6f5-f24a-5172-b528-8419d2c49027](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/degree-excess-among-bearers-is-more-in.json) — OPEN analyst calibration (other direction, bearers only, every respect): if x and y both have r and x's represented degree of r is strictly higher than y's, x is more r than y. |
| 37 | [ed766869-09b3-529a-ad3d-f817a931b5a3](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/no-degree-below-null.json) — OPEN analyst premise: no represented degree of any perfection lies below the null degree (lacking the perfection altogether). |
| 38 | [ee4ab504-c8fe-59bc-bc96-7cbeefed6410](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/excluded-middle.json) — Excluded middle as a general principle: every proposition either holds or does not hold (∀ p, p ∨ ¬p). |
| 39 | [ef068f46-6d3f-4a7a-b1b9-36e52d9fe867](https://github.com/moritzbrantner/truth-core/blob/960fe26728cee3f3467950d3aab67ded6cf2eb39/corpus/statements/ef068f46-6d3f-4a7a-b1b9-36e52d9fe867.json) — OPEN analyst premise, attribution deferred (agency in act, restricted to causes of being): whatever causes the being of something (CausesIn c x esse, CAUSE_2 at esse) is in act in some respect (InAct c r for some r). It is the sibling, for the tenseless CausesIn at esse, of STMT-AQUINAS-OPERATION-ONLY-OF-BEING-IN-ACT (every cause along an Ontic.Causes edge is in act in some respect, after q.75 a.2 co. 'non enim est operari nisi entis in actu', claim f4b1c499) and of q.25 a.1 co. ('unumquodque, secundum quod est actu et perfectum, secundum hoc est principium activum', claim a5d11a9e); those claims are not attributed this CausesIn statement. Meaning: a cause of being that is in act in no respect would be nothing and could do nothing. It is weaker than 'Whatever causes the being of anything is itself in act as to being' (it names no respect), which entails it (lemma inActOfHasBeing, not registered, to avoid a support cycle). CausesIn at esse is read here for extrinsic (efficient) causes of being, after the paradigm of DEF-CAUSE-OF-PERFECTION (fire causing heat); intrinsic principles are not CausesIn edges on this reading. DEF-CAUSE-OF-PERFECTION itself does not state that restriction: if CausesIn counted prime matter as a material cause of the composite's being (in act in no respect), this premise would fail for it; an unread lead, recorded with no weight. No independent warrant is recorded for it. |

### Calculation validation and reproducibility

The calculation first solves each strongly connected component in dependency order, starting from the permitted input variables. Canonical Boolean equality detects the fixed point. For monotone F, its exact minimal-support family is:

$$M=F\land\bigwedge_{v\in\operatorname{support}(F)}(\neg v\lor\neg F[v:=0]),$$

with every irrelevant manager variable fixed false. This enforces that every included premise is needed within its selected set. Counts use arbitrary-precision integer traversal, including skipped-variable factors and complemented edges; they are not floating-point estimates.

Verification completed:

- A small exhaustive fixture agrees with the existing `configurations.implication_closure` antichain helper, including grounded/ungrounded cycles and a zero-premise theorem.
- Independent Boolean forward chaining agrees on 770 deterministic input sets for both targets: 1,540 comparisons.
- Five minimum-size example packages for each target derive their target; every single-member deletion fails to derive it.
- Both saved minimal-family diagrams satisfy `M → F`, all 570 relevant single-input deletion constraints, and all 630 outside-support variable exclusions across the two targets. A separate Shannon-recursion minimizer produces exactly the same diagrams.
- One complete 39-input G package has a checked forward replay through 30 ordered registered result rules. This is an argument-graph replay, not a newly elaborated Lean proof term.
- An independent JavaScript BigInt traversal of the exported diagram reproduces both counts, agrees with both complete size histograms, verifies all ten displayed sample assignments, and checks the order of all 284,850 diagram edges.
- `truth frontier-diff --base HEAD` reports no premise or support-bundle change for this documentation-only work.

The downloadable calculation contains the canonical graph/dictionary, exact diagrams, count/size summaries, representative proof traces, the one-off symbolic calculation script and independent-count evidence. The script is analysis tooling, not an additional repository runtime or status authority. The canonical corpus and Rust CLI retain their current roles.

## Scope audit: independence and possible separate existence (2026-11-13)

This audit uses the same registered graph and terminal basis as the calculation above (current main at `03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`). It does **not** change the formal status of a premise, delete a conditionally valid result, or substitute a countermodel for a proof of its negation in every interpretation.

The companion [priority and independence investigation](priority-independence-logic-support-investigation.md) now supplies a constructive conditional separation route and a weaker consumer-local argument proposal. Neither is registered as a new proof or silently substituted for the unrestricted premise here.

### A concrete modal countermodel

`DEF-DEPENDS-FOR-BEING` makes `DependsForBeing y x` a primitive counterfactual/explanatory relation, including counterpossible contexts. It is **not** definitionally the negation of `CanBeWithout y x`. `DEF-CAN-BE-WITHOUT` says there is a real possibility in which `y` exists and `x` does not. The existing `Ontic`, `NecessaryAt` and `ContingentAt` in `TruthCore/German/Kant/CosmologicalInference.lean` supply a precise possible-worlds test, without reinterpreting these primitives.

Let the world and being carriers each be `Bool`, with universal accessibility from the actual world `false`. At every accessible world both beings (`y = false`, `x = true`) exist. Set `DependsForBeing a b := (a = true ∧ b = false)` and `PriorSimply := False`. Interpret `CanBeWithout a b` exactly as `∃ v, access false v ∧ ExistsAt v a ∧ ¬ ExistsAt v b`. Hence:

| Statement in this finite interpretation | Value |
| --- | --- |
| `NecessaryAt x` and `NecessaryAt y` | True |
| `DependsForBeing x y`; `¬ DependsForBeing y x` | True; true |
| `CanBeWithout y x`; `CanBeWithout x y` | False; false |
| `DependenceExcludesBeingWithout`; `PriorityByBeingWithout` | True; true |
| `IndependenceAllowsBeingWithout`; `NonmutualDependenceSufficesForPriority` | False; false |

Thus an effect `x` can be necessary while depending asymmetrically on `y`; the existing relations do not prohibit this. The Lean omission model `Control.nonmutualDependenceSuffices.omit_hAllow` already has **exactly these** `DependsForBeing`, `CanBeWithout` and `PriorSimply` truth tables, with `nonmutualDependenceSuffices_omit_hAllow` checked by `decide` and included in the certified round-2 controls. The universal-accessibility/necessary-existence interpretation is a finite modal extension checked separately by exhaustive truth-table evaluation, **not** an additional Lean-certified bridge equating dependence with possible-world existence. This is a counterexample to the unqualified bridge for an admissible interpretation, not a proof that necessary dependent beings exist in reality.

Even the restriction `ContingentAt x → (¬ DependsForBeing y x → CanBeWithout y x)` is **not** forced by the repository's unconstrained primitive: take two universally accessible worlds, with both beings existing only at the actual world, the same asymmetric dependence as above, and no world where `y` exists without `x`. `x` is contingent, yet the restricted bridge fails. To endorse it requires an additional semantic account under which failure of the counterfactual of dependence, when `x`'s absence is genuinely possible, supplies a joint `y ∧ ¬x` world. This second finite model tests logical non-entailment from the primitives; it is not a counterexample to every more restrictive theory of counterfactuals.

### Scope choices and the defensible replacement

Write `D(a,b)` for `DependsForBeing a b`, `S(a,b)` for possible separate existence, `C(x)` for contingency at the selected world and `P(a,b)` for simple priority. The old bridge is `∀ y x, ¬D(y,x) → S(y,x)`.

| Candidate | Exact content | Consequence |
| --- | --- | --- |
| Localize to nonmutual dependence | `∀ y x, D(x,y) → ¬D(y,x) → S(y,x)` | Sufficient for the *existing* proof but still fails for necessary `x`. Not a repair by itself. |
| Restrict to a contingent effect | `∀ y x, C(x) → D(x,y) → ¬D(y,x) → S(y,x)` | Weakest useful **scoped nontrivial** modal bridge for that proof pattern. Still **OPEN** under the primitive interpretation; yields only contingent-effect priority unless every relevant effect's contingency is separately established. |
| Make independence modal | Define modal non-separability as `¬S(y,x)` | Its negation entails `S` by classical logic, but this is **not** the existing explanatory `D`. Equating them would hide the disputed bridge in a definition. |
| Bypass possible separation | Accept `STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY` directly: `∀ y x, D(x,y) → ¬D(y,x) → P(y,x)` | The existing **OPEN** intermediate gives general priority without pretending to derive modal separability. It is a direct support option, not a newly proved theorem or independent warrant. |

No unique weakest *philosophically warranted* bridge follows from the existing meanings. The recommended correction is to **retain** the old verified conditional theorem with its explicitly overstrong OPEN input, **not** present that input as warranted, and use the already recorded direct nonmutual-priority proposition for unrestricted applications. Keep the contingent-effect bridge as a candidate for a *separate scoped result* once its counterfactual semantics and an appropriate use site are fixed. In particular, do not strengthen it by declaring all dependent effects contingent. Its remaining commitments are the semantics of counterfactuals with impossible antecedents, which worlds count as really possible, and why nondependence—rather than mere absence of a causal edge—supplies a separability witness. Also keep the existing natural-priority-to-`SIMPLY_PRIOR_1` bridge openly qualified.

### Exact effect on recorded support

There is exactly **one registered rule** using `STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT`: the three-premise `NONMUTUAL-DEPENDENCE-PRIORITY-FROM-BEING-WITHOUT` result. Its conclusion `N = STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY` has no other registered deriving rule; one immediate consumer obtains `E = STMT-EFFICIENT-CAUSE-IS-PRIOR-TO-EFFECT`. The existing Lean proof uses the strong input only at `hAllow y x hyx`. Other arguments that consume `N` or `E` **do not themselves assume this strong premise** if those intermediate statements are taken directly. The 13 immediate G rules and nine irredundant direct conjunctions are unaffected.

Let `d`, `i`, `r`, `n` be the direct-input variables for dependence excluding being-without, the disputed independence bridge, the priority-by-being-without criterion and `N`, respectively. The complete direct-or-derived system has the exact local equation

$$F_N=n\lor(F_D\land i\land F_R).$$

All three of `D`, the disputed `I` and `R` are terminal inputs with **no other rule consumer**; `N` has this single incoming rule. Consequently, in the original terminal-only projection there is an exact factorization `Φ_G^T = d ∧ i ∧ r ∧ K_G` (and analogously for H), where `K_G` contains none of `d,i,r,n`. This is a graph-structural factorization of the existing exact support family, not an independence claim about its philosophical premises.

| Explicit graph/input scenario | G minimal sets | G size range | G shared inputs | H minimal sets |
| --- | ---: | --- | ---: | ---: |
| Original terminal-only expansion (`d ∧ i ∧ r`) | 67,798,928 | 39–149 | 9 | 109,971,456 |
| Original 368 terminal inputs, with `i = false` and intermediate inputs still disabled | **0** | — | — | **0** |
| Replace the deriving rule by direct input `n`, **recomputing** the terminal basis | 67,798,928 | 37–147 | 7 | 109,971,456 |
| Permit `n` directly **as well as** `d ∧ i ∧ r` in a hybrid terminal basis | 135,597,856 | 37–149 | 6 | 219,942,912 |

The third line is a **basis change**, not preservation of the original 368-input question: `N` becomes a terminal, and `D`, `I`, `R` leave the G/H backward slice. The exact bijection replaces `{d,i,r}` in each inclusion-minimal support with `{n}` (size −2); the original number of conjunctions is therefore unchanged. The fourth line has two incomparable variants of each `K` package, giving twice the original number. The six unaffected universally shared G inputs remain shared; the third line adds `n` as the seventh. A 39-input minimum package from this note was forward-replayed and remained minimal after the three-for-one replacement (37 inputs). These counts follow exactly from the existing verified graph structure and the exact original support-family counts; they do not treat bounded Rust route or antichain diagnostics as a full DNF enumeration.

For the **unrestricted** 599-direct-input system, forbidding `i` leaves `F_N = n`, not false: direct acceptance of `N`, `E`, the stronger root H, and many other intermediate statements remains available. The all-input fixed-point graph still defines the exact formula, but the corpus note does not claim a flattened all-input minimal-set count. Removing the bad premise as an accepted *warrant* likewise does not logically refute it or invalidate the original conditional Lean proof; it changes which input bundles one considers defensible, not which conditionals are derivable in the registered graph.

## Esse-cause priority without separability (#1604, 2026-11-14)

This section records a sibling path to priority that uses neither `DependsForBeing` nor any possible-separation premise. It adds registered rules, so the snapshot counts above describe the earlier graph and were **not** recomputed.

### What is verified

All results are in `TruthCore.Results.Causality.EsseCausePriority` (spec `specs/esse-cause-priority.toml`, attempt `520ea849-31eb-4f63-88b9-77bce198b63d`). Every premise is OPEN; each conclusion holds only under its listed premises.

| Result | Premises | Conclusion |
| --- | --- | --- |
| `actualEsseCausePriority` | esse cause is actual concrete ground (cb1cdea9); actual grounding is simple priority (7a63a3fe) | b50fb858: a distinct cause of the esse of an actual concretum at w is SIMPLY_PRIOR_1 to it |
| `distinctEsseCausePriority` | b50fb858; caused esse is had (2f2f5bd2); act of esse suffices for existence at w (546975ef); esse in re is concrete in the profile (2d9807a5) | ee74c678: a distinct cause of a thing's esse is SIMPLY_PRIOR_1 to it |
| `firstBeingNoPotencyOfEssePriority`, `weakOfEssePriority` | first being in some act (8288ff1e); act and potency make composite (3d99779b); composite has a distinct cause of its being (ca07cae9); ee74c678 | 0cf675c4 and 61ad11f3 |
| `noComponentFirstOfEssePriority` | 86f10ec3; 61ad11f3; c6d6379b; participated esse has a distinct cause (732302a1); ee74c678 | 09c6d5f0: no component is the first being |

The controls (`Control.Certificate`) give a joint witness with a nonvacuous esse cause, an omission model for each priority bridge and for the caused-esse premise, and a model in which ee74c678 holds while efficient-cause priority on the same relation fails for a self-cause. ee74c678 says nothing about self-causes or respects other than esse. The consumers that need those instances (no self-cause, causal well-foundedness, per se loops, the secunda via) therefore still need `STMT-EFFICIENT-CAUSE-IS-PRIOR-TO-EFFECT` (E).

### Where the unscoped path was used

N is used only through E. The consumers of E rederived here are `firstBeingNoPotencyOfComposition`, `weakOfComposition` and `noComponentFirstOfWeak`/`noComponentFirst` (09c6d5f0 feeds most God and root routes). Each applies E at exactly one instance, `(c, f, esse)`, where `c ≠ f` and `CausesIn c f esse` hold for a supposed first being `f`, and only to obtain `PriorSimply c f`. Those instances satisfy the `c ≠ x` and `CausesIn … esse` antecedents. They do not satisfy `ActualConcrete m w f` from their own premises, because no profile occurs in them. The three scope statements supply it: a caused esse is had, what has esse exists at w, and what has esse in re is concrete (the adopted CONCRETE_6 calibration). The q.3 a.7 cause and the esse-cause bridge use one relation, DEF-CAUSE-OF-PERFECTION at esse, so the new arguments need no bridge to efficient causing. The route avoids e0088de9 only because cb1cdea9 covers every `CausesIn … esse` instance. If perfection-causing includes non-efficient exemplar or final causes, cb1cdea9 inherits e0088de9's recorded failure condition in stronger form: it would make such a cause concrete, existing at w and a ground. The component route uses 732302a1 rather than 2b25a78c. They have the same body, but 2b25a78c links the external efficient esse-cause sense, a recorded defect that is left unchanged here. The Theta.8 routes (6df393c4, ae809bfd) apply E in the same pattern and were not rederived.

The definition links of 7a63a3fe were corrected. It linked the root definition (c57e2682) and the ancestry definition (c86cc1d1), two senses of WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT that its content does not use. It now links the actual-concrete-grounding-edge definition (a1b2e330).

### Structural effect, computed exactly

Forward chaining over every registered argument with a result record (no counting) gives these facts:

- **On main:** with every terminal input except `i` (STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT), neither G nor H is derivable. This agrees with the zero line above.
- **With this change:** both G and H are derivable without `i`. One greedy inclusion-minimal `i`-free terminal package for G has 41 inputs and contains neither `d` nor `r`. The exact factorization `Φ_G^T = d ∧ i ∧ r ∧ K_G` therefore no longer describes the graph.
- **Cost in the terminal-only basis:** cb1cdea9 is an intermediate there, and its only registered derivation runs through the dependence route: 2068f91c, the esse effect depending on its cause, and ActualDependenceIsGrounding 2e248016, which #1590 owns. Each of 2068f91c, 2e248016 and 7a63a3fe lies in every `i`-free terminal G package. So the terminal-only system trades the separability premise for the dependence-to-grounding bridge. It does not remove dependence premises.
- **With cb1cdea9 taken directly** (unrestricted basis): G is derivable without `i`, 2e248016, 2068f91c, c0d99549 (an effect depends for being on its efficient cause) and N. H is derivable with cb1cdea9 direct and without `i`, 2e248016, 2068f91c or N (each removed singly), but not once c0d99549 is also removed. H thus keeps a dependence input elsewhere.

The exact numbers of inclusion-minimal sets for G and H after this change need the off-repository symbolic calculation and are not claimed.

### Why causing esse grounds, and why grounding is priority

**Causing esse is grounding.** DEF-CAUSE-OF-PERFECTION reads `CausesIn c x esse` as effective causal responsibility for x's being, not merely for its coming to be (`docs/notes/causal-perfection-transfer.md`). If c is effectively responsible for the being that x actually has at w, then x's being at w is partly accounted for by c. That is the job of the selected world-local relation `grounds w` among actual concreta. The bridge cb1cdea9 records this identification as one direction only: being the effective source of an actual thing's being makes one its actual ground.

The passage from tenseless `CausesIn c x esse` to "the being that x actually has at w" is not part of DEF-CAUSE-OF-PERFECTION. It is the sustaining reading: the passage from CAUSING_AN_EFFECT_3 to CAUSING_AN_EFFECT_5 (SustainsBeing, the CAUSE_OF_BEING_2 definition) of DISAMB-BECOMING-BEING-CAUSE, which the repository records as the OPEN bridge 23e04ae5. cb1cdea9 thus carries that reading at the selected world.

**The limit.** The bridge needs the causa essendi reading. A merely originating cause (causa fiendi, the builder of a house, q.104 a.1) is responsible for the house's coming to be, not for its continuing being. Such a cause need not ground the house at w and need not exist at w. `CausesIn` has no built-in sustaining or temporal law, so that reading is an OPEN semantic burden of cb1cdea9. Its record already says so.

**Grounding a thing's being is priority.** SIMPLY_PRIOR_1 is priority of nature, not of time: the posterior's being presupposes the prior's. A ground of x's being at w is something x's actual being presupposes. 7a63a3fe says only this direction. The asymmetry of priority is not part of it. On the routes, asymmetry comes from separate OPEN premises (grounding asymmetry or well-foundedness among actual concreta, priority requires nonmutual dependence). PriorSimply stays a primitive constrained only by such premises.

### Rivals priced

- **An esse-cause as an enabling condition without existential grounding.** *Target:* cb1cdea9. *Mechanism:* c's activity is needed for x's continuing to exist, but c only removes impediments or supplies conditions (q.104's remover of an impediment; the guard and supply examples of the causal-perfection-transfer note), so x's being is not grounded in c. *Independent justification:* enabling conditions without production are familiar and are distinguished by Aquinas himself. *Conflict:* DEF-CAUSE-OF-PERFECTION excludes "mere enablement" from `CausesIn`. An enabler is therefore not a `CausesIn … esse` instance, and the bridge's antecedent fails rather than its consequent. The rival's real target moves upstream, to ca07cae9 and 732302a1, the premises that a composite or participated thing has an effective cause of its being and not only enabling conditions. That is the existing uncaused-composite rival, now carried without any separability premise. This pricing covers only enablers. It does not show that every effective cause of an actual thing's being grounds it: the next rival is a standing case against that.
- **Existential inertia: a non-sustaining esse-originator.** *Target:* cb1cdea9. *Mechanism:* a strict originator of esse is a `CausesIn … esse` instance. DISAMB-BECOMING-BEING-CAUSE reads OriginatesBeing, taken strictly, as time-indexed CAUSING_AN_EFFECT_3. Such an originator need not exist at w or ground x there, so cb1cdea9's consequent fails. *Independent justification:* that disambiguation, and the existential-inertia rival recorded on the sustaining bridge 23e04ae5 (persisting things need no concurrent sustaining cause; Schmid 2021, recorded there as read). cb1cdea9's own note says its sustaining interpretation needs separate defense. *Price:* there are two options. (a) cb1cdea9 fails for strict originators. (b) `CausesIn … esse` is read as sustaining; then ca07cae9 and 732302a1 must deliver *sustaining* causes for the composite or participated first-being candidate, which the inertia theorist denies. Either way, the burden is in substance 23e04ae5's. The route's escape from separability is paid for with the sustaining reading. This rival is unresolved here.
- **Metaphysical interdependence (mutual grounding).** *Target:* the use of 7a63a3fe together with asymmetric priority. *Mechanism:* if two actual concreta ground each other, 7a63a3fe makes each prior to the other. Navigation only, attribution deferred: N. Thompson, "Metaphysical Interdependence", in M. Jago (ed.), *Reality Making* (OUP 2016). *Conflict:* this contradicts the routes' separate grounding-asymmetry premises, not the implication 7a63a3fe states. Where it bites, it is a rival to those premises. For the esse-cause instances here it would need an actual effect to ground its own esse-cause, and no such case is identified.

## Dependence to priority through actual grounding (#1590, 2026-11-14)

This section tests the route `ActualConcrete w c ∧ ActualConcrete w x ∧ DependsForBeing x c` → `grounds w c x` → `PriorSimply c x`. As in the previous section, the snapshot counts above were **not** recomputed.

### What is verified

All results are in `TruthCore.Results.Causality.DependenceGroundingPriority` (spec `specs/dependence-grounding-priority.toml`, attempt `040e3b4e-f59c-4ef4-9b5a-7cc181b5bde4`). Every premise is OPEN. Each conclusion holds only under its listed premises.

| Result | Premises | Conclusion |
| --- | --- | --- |
| `actualDistinctDependencePriority` | distinct-relata dependence-to-grounding bridge (a8298fbd); actual grounding is simple priority (7a63a3fe) | 0791f2ad: if an actual concretum depends for its being on a *distinct* actual concretum c, c is SIMPLY_PRIOR_1 to it |
| `actualEsseCausePriorityViaDependence` | 0791f2ad; caused esse depends on its cause (2068f91c); esse causes exist at w (c99f9d23); esse causes are concrete (82eeeb3c) | b50fb858, the #1604 esse-cause priority node, by a second route |
| `firstBeingNoPotencyOfThetaEightEsse`, `weakOfThetaEightEsse` | the four Theta.8 premises (ca55ed3a, d017b6b0, d8024a38, ca07cae9); ee74c678 | 0cf675c4 and 61ad11f3, without efficient-cause priority E or the cause-to-efficient bridge e0088de9 |
| `esseCauseGroundViaDistinctDependence`, `esseCauseGroundOfExistentConcretenessViaDistinct` | the premises of the two existing derivations of cb1cdea9, with a8298fbd in place of 2e248016 | cb1cdea9 |
| `simplyPriorGroundViaDistinctDependence` | the premises of `simplyPriorGroundViaDependence`, with a8298fbd in place of 2e248016 | 86efed1a |
| `reflexiveUnrestrictedExcludesActualConcreta` | everything depends for its being on itself (56252cd8); 2e248016; 7a63a3fe; priority requires nonmutual dependence (47aff057) | cec081d8: no actual concretum at w |

The Comparator-checked corollary `actualNonmutualOfDistinct` derives N (STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY) **restricted to actual concreta** from 0791f2ad, because the nonmutuality antecedent already excludes `y = x`. N itself is not derived: it also covers non-actual and non-concrete relata. The controls (`Control.Certificate`) give a model in which D is reflexive and a8298fbd, 7a63a3fe and 47aff057 hold together with a nonvacuous priority instance. On that model the unrestricted bridge 2e248016 fails. They also give an omission model for each bridge of the scoped route.

**Honest size of step 1.** `actualDistinctDependencePriority` is a plain composition of two existing bridges. Its content lies in what it avoids: it uses no separability premise, and it does not use the unrestricted bridge, which the next point shows to be load-bearing in a bad way.

### Why the distinct-relata bridge matters on the root route

`reflexiveUnrestrictedExcludesActualConcreta` certifies the step that result d86e618b left elementary. Reflexive D (an OPEN reading of DEF-DEPENDS-FOR-BEING's bare counterfactual clause, #1593) with 2e248016 makes every actual concretum ground itself. 7a63a3fe then makes it prior to itself, and 47aff057 then requires it both to depend and not to depend on itself. 47aff057 lies in every terminal G package, and the #1604 `i`-free route uses 2e248016 and 7a63a3fe. That route is therefore consistent only with a strict, non-reflexive reading of D among actual concreta. The new siblings take a8298fbd wherever the old derivations used the bridge only at distinct relata, and the controls show that this bundle has a model with reflexive D.

### Use-site test (#1590, step 2)

The Theta.8 routes 6df393c4 and ae809bfd reach N only through E, which is derived from N, c0d99549 (an effect depends for being on its efficient cause) and 47b151ca (an efficient cause does not depend on its effect). N in turn is derived from d, i and r. Both routes apply E at exactly one instance: `(c, f, esse)` with `c ≠ f` and `CausesIn c f esse`, where c is the distinct uniting cause that ca07cae9 gives a composite first-being candidate f. ee74c678 covers that instance, so the instances used lose nothing. The meaning of the conclusions is unchanged. No premise says that f can exist without c, so the necessary-cause failure of `i` does not arise.

The net replacement in this subderivation is as follows.

- **Removed:** E, and with it N, `d`, `i`, `r`, c0d99549 and 47b151ca; also e0088de9.
- **Added**, along the dependence route to ee74c678: a8298fbd (or 2e248016), 7a63a3fe, 2068f91c, c99f9d23 and 82eeeb3c. Then the #1604 actuality-scope statements 2f2f5bd2, 546975ef and 2d9807a5, which give ee74c678 from b50fb858.

The dependence premise 2068f91c replaces c0d99549. It is narrower: it covers only distinct causes of esse.

### Structural effect, computed exactly

These facts come from forward chaining over every registered argument with a result record. The terminal basis is every statement with no incoming rule. The script is analysis only, not repository tooling.

- **Terminal-only basis:** unchanged. a8298fbd is an intermediate whose only derivation is from 2e248016 (cc7dd608). So 2e248016 still lies in every `i`-free terminal G and H package, here as before.
- **a8298fbd taken directly, without `i` and 2e248016:** on main neither G nor H is derivable. With this change both are. One greedy inclusion-minimal package for G has 41 inputs and contains none of d, r, c0d99549, N, E or e0088de9; it contains 7a63a3fe. G stays derivable without c0d99549 as well. H is not derivable once c0d99549 is also removed, so H keeps a dependence input elsewhere.
- **`truth frontier-diff --base 4a5b5c0e9`:** open premises reaching the root stay at 476 (339 bare, 90 supported, 47 stated). Verified support alternatives rise from 462 to 468. a8298fbd now reaches the root. No bare premise is added and no premise is established.

Consumers of 2e248016 that were **not** moved, with the reason:

- `contingentGroundedViaDependence` (dd7ee4b9): 3ef67739 does not require a distinct dependee.
- `necessityCauseGroundViaDependence` (eddef85a): its conclusion d29cebca links both WELL_FOUNDEDNESS_AND_ANTI_BRUTE_ROOT senses although its type uses neither. This is the same sense-link defect as on STMT-ACTUAL-GROUNDING-ASYMMETRIC, so a new argument concluding it fails the sense-mixing check.
- `perSeFromGrounding` (4fd4e8f7): it mixes the NECESSARY_3/4/11 senses and is allowlisted, and a sibling would need a sense bridge.

The Lean proofs of the last two siblings are one-line changes, and the third is not. All three are follow-ups.

### Semantic burden

**Which reading of `grounds` the bridge needs.** `grounds w` is the profile's primitive selected relation (a1b2e330). It is not Fine's formal strict ground, which is sense 2 of 23dd6f32 and a different Lean declaration. #1600 found that the constitutive reading of ground fails on DEF-DEPENDS-FOR-BEING's own paradigm: the sun's existing does not constitute the light's. On that reading a8298fbd would be false of the paradigm edge. The bridge is plausible on the **causal-explanatory** reading, sibling (b) of 23dd6f32, which the #1604 section already uses for cb1cdea9: c grounds x at w when x's being at w is accounted for by c's actual causal responsibility. The paradigm fits that reading exactly. The light in the air is while the sun shines and ceases when the sun ceases, which is Aquinas's own example of a causa essendi (q.104 a.1). So the sun, an actual concretum distinct from the light, accounts for the light's being at w. The other OPEN premises that constrain `grounds` (roots as ungrounded actual concreta, grounding asymmetry or well-foundedness) must then be read on the same causal-explanatory reading. Neither Lean type encodes that reading.

**Why grounding of existence is priority.** Take the same example. The sun is prior by nature to the light, though not in time: the light's being presupposes the sun's shining, and the sun's being does not presuppose the light. 7a63a3fe generalizes this one direction to every grounding edge between actual concreta. What the scoped route gives is the primitive SIMPLY_PRIOR_1 relation from the grounding of x's *being*. In #1595's terms it is not priority in every respect of x's existence. Asymmetry still comes only from separate OPEN premises; the #1604 section prices the mutual-grounding rival.

**Rival: dependence by origin.** *Target:* a8298fbd and 2e248016. *Mechanism:* on the bare counterfactual clause of D, x depends on c whenever x would not be if c were not. By the necessity of origin, a child would not be if its parent had never been. (Navigation only, attribution deferred: Kripke, *Naming and Necessity*, Lecture III.) While the parent is alive, both are actual concreta, they are distinct, and D(child, parent) holds. Yet the parent does not account for the child's being at w: it is a causa fiendi, like the builder of a house (q.104 a.1). So the bridge's consequent fails. *Independent justification:* the necessity-of-origin judgment is widely held independently of this argument, and the fiendi/essendi distinction is Aquinas's own. *Price:* DEF-DEPENDS-FOR-BEING qualifies D as an effect's relation to its *agent cause*, after q.44 a.1 ad 2. Read with that qualification as dependence on a cause of being, D excludes the origin case and a8298fbd survives. Read as the bare counterfactual, D includes it and a8298fbd fails for originators. On the route, D instances enter only through 2068f91c (a distinct cause of esse) and 47aff057 (from priority). So the choice comes down to whether a `CausesIn … esse` cause sustains its effect. That is the sustaining bridge 23e04ae5, where the existential-inertia rival (#1616) already stands. The dependence route therefore relocates the separability burden onto the sustaining reading, exactly as the #1604 esse-cause route does. It adds no independent escape.

**Reading boundary: bare modal requirement.** If D were read as `□(Exists x → Exists c)`, two necessarily coexisting actual concreta would each depend on the other. a8298fbd, 7a63a3fe and 47aff057 would then be jointly inconsistent for them. DEF-DEPENDS-FOR-BEING excludes that reading ("not necessitation"), so this is a scope condition on D, not an objection to the bridge. No such pair of concreta is identified.

### Provisional judgment

The scoped route is a valid conditional composition. On the root route it is better supported than the unrestricted bridge: it gives the same God-existence support without committing D to irreflexivity, which the unrestricted bridge does as soon as 7a63a3fe and 47aff057 are present. a8298fbd is plausible for D's causal paradigm on the causal-explanatory reading of `grounds`, and implausible on the constitutive one. Its standing rival, dependence by origin, is defeated only by the agent-cause (causa essendi) qualification of D, so its warrant stands or falls with the sustaining reading 23e04ae5. The following would revise this judgment:
- a defense of 23e04ae5 against existential inertia (#1616), which would discharge the origin rival on the route; or
- a derivation of a8298fbd that does not pass through 2e248016, which would change the terminal-only basis.
