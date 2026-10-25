# Modal research fixture

Issue #261 supplies shared mathematical infrastructure for the modal-system
experiments indexed by #248. It introduces no metaphysical axiom, source reading,
new modal logic, ontology, or solver service. The K/D/T/S4/B/S5 experiments remain
separate work.

Import `TruthCore.Modal.ResearchFixture` for proposition domains and local collapse;
import `TruthCore.Modal.ResearchFinite` for finite executable models. These reuse
`TruthCore.Modal.Frame`, `Formula`, `Holds`, and the Scott embedding's `MProp` and
`Box`. `full_iff_hume` proves agreement with the existing Hume `Collapse`; none of
Scott's positivity, essence, existence or theological axioms are hypotheses.

## Three proposition scopes

| Domain | Quantification | Root equality predicate admissible? |
| --- | --- | --- |
| `allPredicates` | Every `W → Prop` | Yes, by definition |
| `expressible F V` | Denotations of every `Formula A`, with fixed atoms, frame and valuation | Only if some formula denotes it |
| `corpusDomain inventory` | Exactly the predicates in a caller-supplied corpus inventory | Only if the inventory contains it |

The corpus inventory parameter identifies the current selected philosophical
propositions; it is not an automatic enumeration of JSON statements and does not
claim that the corpus is complete. Formula expressibility also depends on the
valuation: merely changing an atom's name does not add a distinguishing proposition.
Each scope is a subset of all predicates. An inventory is a subset of a fixed
language only when the caller supplies that inclusion; `restrict` transports
collapse along any such inclusion.

`MC F D w := ∀P, D P → P w → Box F P w` is relative to root `w` and domain `D`.
It does not assert global validity, global uniqueness, possible collapse, necessary
collapse, or conceivability of collapse. No accessibility condition is implicit.

## Exact assumptions and world identity

| Result | Assumptions beyond the supplied frame/domain/root |
| --- | --- |
| `identity_separates` | Root identity predicate is admissible; `MC` at that root |
| `full_iff_hume` | None; exact full-domain equivalence |
| `restrict` | Explicit domain inclusion; `MC` for the larger domain |
| `collapse_agreement` | Excluded middle; closure under negation; root `MC` |
| `extensional_separates` | The preceding assumptions plus world propositional extensionality |
| `eval_correct` | Finite enumeration contains every world; Boolean edges and atomic valuations as supplied by `Model` |

`Agree D w v` means agreement on every predicate in D.
`PropositionalExtensionality D` says such agreement identifies the two world labels.
It is separate from Lean's axiom named `propext`. It becomes a contested
metaphysical commitment if D is said to contain all complete propositions and the
labels are said to denote metaphysical possibilities. The fixture makes neither
claim. Distinct duplicate labels are not presented as distinct metaphysical
possibilities. Full predicate comprehension already includes `v = w`, so its
separation proof uses neither extensionality nor excluded middle.

The `duplicates` model has universal accessibility and a constant atomic valuation.
All formulas agree at its two Bool labels. Language-relative MC holds, while root
identity-predicate admissibility and domain-relative world extensionality both fail.
The `branching` model distinguishes the scopes further: a constant-true corpus
inventory has MC at `false`, but the fixed language (which contains a distinguishing
atom) and the full predicate domain do not. These are exact model witnesses, not
arguments that a philosophical proposition is contingent in reality.

## Reproduce finite evaluations

```bash
lake build
lake env lean --run scripts/modal-fixture.lean
scripts/verify-result.sh MODAL-FIXTURE-CHECKS
```

The report lists roots in `[false, true]` order. Each row contains:

```text
(root, [(target, accessible), ...], atom truth, box truth, diamond truth,
 atom→box(atom), accessible atom witnesses, accessible counterexamples to box(atom))
```

Expected report:

```text
[(false, [(false, true), (true, true)], true, false, true, false, [false], [true]),
 (true, [(false, false), (true, true)], false, false, false, true, [], [true])]
```

`Model` keeps frame and valuation separate, lists every world explicitly, and
requires a proof that no world was omitted. `eval_correct` proves its Boolean
interpreter agrees with `Holds`, including implication, box and diamond.
`witnesses` and `counterexamples` filter accessible worlds in enumeration order.
`collapseEval` checks only a supplied finite list of Boolean predicates; it does
not enumerate arbitrary Prop-valued functions or prove unrestricted MC.

Build-time `#guard` assertions cover both roots, box/diamond, predicate-inventory
collapse and a dead-end world's vacuous box/false diamond. The result contract
`ResearchFinite.Checks` additionally includes the general evaluator theorem, scope
countermodels, root implication values and exact witness lists. Its frozen
Challenge and proved Solution are bound by the corpus and checked by Comparator
with `permitted_axioms: []`, including NanoDa. Conditional excluded middle is an
explicit hypothesis inside a law, never an added axiom or established premise.
