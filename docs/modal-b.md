# B: collapse propagation needs symmetry, not S5

These are stipulated mathematical experiments for #266, the B slice of the
modal-system family in #248 under Hume campaign #247. `Frame`, `MC`, `Dia`,
`Box`, domains and the finite evaluator are the shared #261 semantics. K's
proved equality characterization is imported, not assumed again. Nothing here
attributes a view to Hume or identifies formal world labels with metaphysical
possibilities. No Catholic-case frontier premise is discharged.

## Positive theorem and exact assumptions

`MODAL-B-LAWS` binds `TruthCore.Results.Modal.B.Laws.checks` to `BResearch.Laws`.
A collapsed witness v with a back-edge v→w and an admissible identity predicate
`x = v` forces w=v. This is the shared `identity_separates` theorem instantiated
at v. In the full domain identity is admissible automatically. If w→v and the
relation is symmetric, v→w follows, so possible full MC implies actual full MC
at w by substitution. Reflexivity and transitivity are unnecessary for this
forward implication; global symmetry can itself be replaced by that one
back-edge. No separate world-extensionality axiom is used.

On a reflexive symmetric (B) frame, actual, possible and necessary full MC are
equivalent at a fixed root. Reflexivity supplies MC→◇MC. MC→□MC
uses K's full-successor identity theorem. The separate
`MODAL-B-NECESSARY-SYMMETRY` theorem binds `B.NecessarySymmetry.checks` and
proves MC↔□MC from symmetry alone: every accessible collapsed successor has a
back-edge to the root and therefore equals it; if no successor exists, K's
characterization applies vacuously. No seriality or reflexivity is needed for
this equivalence. Symmetry supplies ◇MC→MC. No
transitivity is added. These are universal conditional theorems, not assertions
that any metaphysical state is possible or actually collapsed.

The assumption bounds have concrete tests. The shared reflexive branching
frame has possible full MC but not actual full MC and is not symmetric. Without
reflexivity the shared dead-end result already gives full MC but no possible
MC, so the B equivalence cannot simply be extended to all symmetric frames.
Identity expressibility matters for world equality: the shared duplicate-label
B frame has modal-language MC without label identity and fails language-world
extensionality. Full comprehension is sufficient but stronger than the exact
witness identity-admissibility condition.

## A restricted language is different from an inventory

`MODAL-B-LANGUAGE-PROPAGATION` binds `B.LanguagePropagation.checks`. It proves
possible domain-relative MC→actual MC on symmetric frames when D is closed
under negation and box and excluded middle is explicitly supplied as a
quantified assumption. Shared collapse agreement along v→w transfers P(w) to
P(v). MC at v gives □P(v). Box closure admits □P itself, and a second MC
application yields □P(w). This proves the conclusion without identity
predicates, world extensionality, reflexivity or transitivity. The theorem does
not establish excluded middle or silently choose it as a permitted axiom.

The full set of denotations of formulas in a fixed modal language (`expressible`)
is distinct from a finite inventory. The former supports the modal constructors;
the latter may omit even □P. The countermodel below uses precisely the one-atom
inventory. It is **not** a countermodel to the closure-qualified theorem.

## Reproduced finite countermodels

`MODAL-B-COUNTERMODELS` binds `B.Countermodels.checks`. The three explicitly
enumerated labels have this symmetric, reflexive edge table:

| from / to | left | middle | right |
| --- | --- | --- | --- |
| left | true | true | false |
| middle | true | true | true |
| right | false | true | true |
| atom p | true | true | false |

Left→middle→right but not left→right proves nontransitivity. Middle has
independent p and ¬p accessible witnesses (left and right), so p is contingent
there. No label has full MC. No label has full-modal-language MC either:
left's □p fails at middle, middle's p fails at right, and right's ¬p fails at
middle. Thus ◇MC and □MC are false at each root in both these domains (each
root has successors and accesses itself).

In the atoms-only inventory, left has MC, middle has possible MC via left, but
middle does not have MC because p fails at right. Box closure fails: □p is true
at left and false at middle although p is true at both, so □p is not the sole
inventory predicate. Evaluator equations reproduce middle's ◇p and ◇¬p as
true, p-witnesses `[left, middle]`, and the □p counterexample list `[right]`.

`MODAL-B-SCOPE-BOUNDARY` binds `B.ScopeBoundary.checks`. It reuses the shared
duplicate-language proofs and branching countermodel, and proves a separate
conditional route: excluded middle, negation closure and D-world extensionality
convert possible D-MC into full MC on symmetric frames. This route exposes all
its assumptions; restricted-language agreement alone is not world identity.
With all predicates the shared K extensionality theorem already proves the
identity criterion; it is not an extra metaphysical premise.

`MODAL-B-DISCONNECTED-SCOPE` binds `B.DisconnectedScope.checks`. A second
finite B model keeps left isolated (only its self-edge), while middle and right
form a separate universal component with the same p valuation. At left actual,
possible and necessary full MC all hold. Left and middle remain distinct and
inaccessible to each other; p is contingent at middle. Hence root-relative
collapse excludes neither other formal components nor contingency at another
root. The theorem never moves the root implicitly.

To reproduce the first table and evaluator lists:

```bash
lake env lean --run /tmp/modal-b-report.lean
```

where the temporary file contains:

```lean
import TruthCore.Modal.BResearch
def main : IO Unit := IO.println TruthCore.Modal.BResearch.report
```

The Boolean evaluator does not claim to enumerate every Prop-valued predicate.
Universal MC claims above are checked by the Lean proofs; the report independently
exposes the finite edges and valuation used by those proofs.

## Proof and interpretation self-sweep

Every result has a separate frozen Challenge and Solution, with no permitted
axioms. The inference records advertise premise-free mathematical facts whose
internal conditional assumptions remain quantified in the proposition. None
uses an opaque bridge premise whose consequent already is the result.

Definitions link the existing frame/domain/MC/identity/agreement/extensionality,
finite-evaluation and model-relative contingency senses, plus the B back-edge,
chain, inventory and closure definitions. The existing scope/identity and
collapse-mode disambiguations are linked alongside the inventory-versus-language
resolution. These specify each root, proposition domain and closure assumption.
There are no new historical source claims or attributed readings to strengthen.
The three scopes (all predicates, full fixed language, finite inventory) are
never exchanged without an explicit theorem or countermodel.
