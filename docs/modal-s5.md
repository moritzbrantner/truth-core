# S5: possible collapse and its exact scope

Issue #267 studies the shared **stipulated mathematical semantics**, not Hume's
historical position or a proof that the represented states are metaphysical
possibilities. The modal operators are the existing Gödel/Scott embedding's
`Box` and `Dia`; no positivity, essence, necessary-existence or theological axiom
is a premise. The separate Scott modal-collapse theorem establishes its own
conditional consequence from its own axioms. It supplies neither metaphysical
possibility nor a warrant for the unrestricted conceivability bridge here.

## Full predicates and the component

`MODAL-S5-LAWS` binds `TruthCore.Results.Modal.S5.Laws.checks`.
It imports the B results rather than assuming a previously proved conclusion:
`B.Laws.possible_full` propagates possible full collapse using symmetry, and
`B.NecessarySymmetry.checks` relates actual to necessary full collapse. K's
proved successor-identity characterization then transports truth.

For an S5 frame (the existing reflexive/Euclidean basis, hence an equivalence
relation), at a common root:

| Consequence | Scope |
| --- | --- |
| `MC ↔ ◇MC ↔ □MC` | All world predicates; root-relative operators |
| Any two accessible worlds agree at every predicate | The root's component |
| `◇P ↔ P` and `P ↔ □P` | Every supplied world predicate P |
| `¬(◇P ∧ ◇¬P)` | Any independently supplied P, at that same root |
| Every supplied label equals the root | Additionally, `Universal F` |

Full comprehension admits `P(v) := v=w`. Thus full MC already forces every
accessible successor to equal the root. No independent propositional
extensionality axiom, excluded middle, `propext` or label-identification
assumption is used on this route. Adopting *all* such predicates as genuine
metaphysical propositions remains an interpretive commitment; Lean's function
space does not defend it.

The stronger imported B results locate the assumptions more precisely than the
S5 specialization: symmetry alone suffices for `◇fullMC → fullMC` and
`fullMC ↔ □fullMC`. Reflexivity supplies the reverse `fullMC → ◇fullMC` and
`□P → P`. Transitivity is unnecessary for those full-domain implications.
The propagation proof needs only the reverse edge from the particular collapsed
witness; its identity predicate identifies that witness with the root. A
universal relation supplies these edges itself, so the extra S5 hypothesis in
the universal-component clause is redundant, not an independent necessity.

S5 alone does **not** make all supplied worlds one component.
`disconnected` has a singleton root component and a separate two-world component.
The root has actual, possible and necessary full MC; `left` fails full MC and is
not the root. Therefore collapse at the root proves no claim about inaccessible
labels. `Universal F := ∀w v, Rwv` explicitly excludes that counterexample.

## A fixed language, an inventory, and identity

`MODAL-S5-LANGUAGE` binds `TruthCore.Results.Modal.S5.Language.checks`. For an arbitrary domain D,
it explicitly assumes negation closure and excluded middle. From possible
D-relative MC, symmetry and transitivity move the collapsed witness to each
world in the root's component. Collapse of P and of ¬P yields agreement; truth
then transports between component worlds. This proves actual/necessary MC,
`◇P ↔ P`, and absence of contingency **for P in D**.

The proof's sharper helper `local_agreement` only needs decisions of admissible
truths at the collapsed witness; global excluded middle in the frozen bundled
contract is a sufficient way to provide those decisions, not a claim of logical
minimality. The existing full formula language is negation-closed by its syntax.
No axiom silently supplies classical reasoning.

Agreement becomes label identity only after the separate
`PropositionalExtensionality D` premise. `Universal F` additionally extends that
identity from the root's component to all supplied labels. Full predicates
already contain identity separators; a limited language need not.

Two explicit tests prevent substituting one domain for another:

- The reused universal `duplicates` model assigns its atom the same truth at
  both labels. All its formula denotations agree, so language MC holds while
  full MC fails. The shared K scope-boundary result also proves language ◇MC
  and □MC there. Restricted-domain world extensionality fails. The separating
  predicate `w=true` is contingent but is **not in that language**; using it
  against language MC would change the quantifier domain.
- `MODAL-S5-DOMAIN-BOUNDARY`, bound to `TruthCore.Results.Modal.S5.DomainBoundary.checks`, uses the
  separating atom as a **one-entry inventory**, not the full formula language.
  That inventory is world-extensional, yet ◇MC at `true` coexists with ¬MC there
  and contingency of the atom: `false` is vacuously collapsed for that inventory.
  Negation of the atom is missing. Thus extensionality alone cannot replace
  negation closure. This is domain-relative vacuity inside a serial S5 frame,
  not the no-successor vacuity of K.

## Countermodels for the assumptions

`MODAL-S5-COUNTERMODELS` binds `TruthCore.Results.Modal.S5.Countermodels.checks` and fixes exact edges,
truth assignments and evaluator witnesses. None establishes real-world
contingency or a metaphysical possibility.

| Assumption removed or scope changed | Reproduced witness |
| --- | --- |
| Single universal component | Singleton root plus isolated two-world component |
| Full expressibility / restricted extensionality | Universal duplicate-label formula model |
| Negation closure, despite extensionality | Universal pair with one separating atom only |
| Sound unrestricted bridge | Universal pair, indiscriminate conception, independent contingency |
| Conceiving MC | Same pair, empty conception, sound vacuous bridge, independent contingency |
| Independent contingency | Universal singleton, witnessed conception, sound bridge and C(MC) |
| Reflexivity for `MC → ◇MC` | Shared sink: MC and □MC, but no ◇MC |
| Symmetry for propagation | Reflexive/transitive branching model below |

`MODAL-S5-SYMMETRY-BOUNDARY` binds `TruthCore.Results.Modal.S5.SymmetryBoundary.checks`. It composes the
existing Hume semantic-test result's reflexive/transitive branching model with
the shared full-MC equivalence. The root has ◇fullMC and independently witnessed
contingency, but ¬fullMC; the reverse edge fails. This makes the symmetry
requirement concrete without dropping reflexivity or transitivity at the same
time. Transitivity needs no countermodel for full propagation because B already
proves it unnecessary. World extensionality likewise is not an additional
assumption for the full-predicate route.

## Conceivability reductio and the open frontier

`MODAL-S5-COLLAPSE-CONCEPTION-EXCLUDED` binds `TruthCore.Results.Modal.S5.Projection.excluded`.
Its three advertised premise statements are deliberately **open**:

1. `STMT-MODAL-S5-SCENARIO-FRAME`: adopt S5 for the supplied interpreted frame.
2. `STMT-MODAL-S5-SCENARIO-BRIDGE`: at this root, every C-conceived predicate has
   an accessible witness. This is actual unrestricted soundness, not necessarily
   soundness of the bridge itself.
3. `STMT-MODAL-S5-SCENARIO-CONTINGENCY`: independently warrant both accessible
   truth values of a supplied P at this same root.

Assume `C(MC)` temporarily (`STMT-MODAL-S5-CONCEIVED-COLLAPSE`, scoped and
discharged by the inference record). The bridge gives ◇MC. The imported B
propagation theorem gives actual full MC; the imported K theorem contradicts the
two independent contingency witnesses. Negation introduction excludes C(MC).
The proof derives this result with typed worlds/accessibility/predicates; it is
not an opaque bridge with the advertised conclusion already in its consequent.

This proves conditional incompatibility, not that any premise is philosophically
true, that C(MC) is genuinely conceivable, or that Hume asserted the unrestricted
bridge. Issue #268 remains the source-fidelity investigation. No new attributed
claim is added here, and no Catholic-case frontier node is closed by this test.

The custom projection exposes the remaining commitments without changing the
Catholic root route:

```bash
python3 scripts/corpus.py frontier --root STMT-MODAL-S5-COLLAPSE-CONCEPTION-EXCLUDED --reaching-root
```

It lists the three scenario premises as bare open premises on the path to the
custom root. Formal closure of a conclusion *from* open premises is distinct
from establishment of those premises. Definitions fix the conditional meanings;
they supply no source evidence for adopting them.

## Reproduction and self-sweep

```bash
lake build
lake env lean --run scripts/modal-s5.lean
scripts/verify-result.sh MODAL-S5-LAWS
scripts/verify-result.sh MODAL-S5-LANGUAGE
scripts/verify-result.sh MODAL-S5-COUNTERMODELS
scripts/verify-result.sh MODAL-S5-DOMAIN-BOUNDARY
scripts/verify-result.sh MODAL-S5-SYMMETRY-BOUNDARY
scripts/verify-result.sh MODAL-S5-COLLAPSE-CONCEPTION-EXCLUDED
```

The report prints the disconnected relation and atom/box/diamond truth at every
label, plus the universal pair's positive/negative witness lists. Exact pair
witnesses are `[true]` and `[false]`; full Prop-function claims are proved by Lean,
not by pretending the Boolean evaluator enumerates every predicate.

Each result above states its premises, derivation and binding theorem. The linked
shared definitions cover frame, domain, MC, identity, agreement, extensionality,
conception, bridge and contingency. The new S5 definitions distinguish equivalence
frames, universal scope, component agreement, finite witnesses, atom inventory
and interpreted scenario. The shared scope/identity and collapse-mode
ambiguities plus `DISAMB-MODAL-S5-COMPONENT-GLOBAL` prevent changes of root,
domain, label identity or metaphysical reading. All Challenges were frozen before
their Solutions; all Comparator configurations permit no axioms. Kernel and
independent checks verify consequence inside these encoded experiments only.
