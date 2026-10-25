# S4 collapse pockets

This is a stipulated mathematical experiment for #265 over the shared modal
fixture. It does not identify metaphysical possibility, attribute a modal system
to Hume, establish real-world contingency or prove a cosmological conclusion.
The result statements have no external premises: their frame, domain and root
hypotheses occur inside the quantified mathematical laws.

## What follows, and why

`MODAL-S4-LAWS` imports the proved K successor-identity theorem rather than
replacing it with a premise. Full-predicate collapse at a world makes every
successor that same world. Transport therefore gives necessary full collapse;
reflexivity supplies the converse. Consequently, in S4 actual full collapse is
equivalent to necessary full collapse. The unrestricted cluster clause says only that
any world mutually accessible from a full-collapsed world equals that world: the
set has at most one member. Reflexivity, hence S4, supplies self-membership and
makes it a genuine singleton. Without reflexivity a dead end has vacuous full MC
and an empty mutual-accessibility set. Terminality alone does **not** make a
cluster singleton: the paired model below has a terminal two-world cluster.

Symmetry would also transport possible full collapse back to the root: an
accessible collapsed world then accesses the root, forcing identity. S4 has
reflexivity and transitivity, and supplies no such reverse edge. The explicit
countermodels verify failure of both symmetry and Euclideanness.

## Reproduced finite models

Both configurations enumerate exactly `root`, `left`, `right`, `twin`.
A row lists its accessible successors:

| World | Paired successors | Unpaired successors |
|---|---|---|
| root | root, left, right, twin | root, left, right, twin |
| left | left | left |
| right | right, twin | right |
| twin | right, twin | twin |

Both are reflexive and transitive. The first atom `p` is true exactly at left.
The second atom is true exactly at twin in the unpaired configuration and false
everywhere in the paired configuration. No edge from either terminal component
returns to root or crosses to the other component.

`S4Research.report true` and `report false` reproduce the full edge and atom
tables plus independent `◇p` and `◇¬p` truth values at every world. The shared
finite evaluator is already proved equivalent to the Prop-valued semantics.
`MODAL-S4-SCOPE-BOUNDARY` additionally freezes exact root witness lists:
`◇p` has `[left]`; the counterexamples to `□p` are `[root, right, twin]`.
Thus contingency is independently specified, rather than inferred from MC.

At the root, in **both** models and **both** proposition domains:

| Test | Value | Witness or reason |
|---|---|---|
| MC | false | root's true `¬p` fails at left |
| ◇MC | true | left, whose only successor is itself |
| □MC | false | root accesses itself and is not collapsed |
| `◇P → P` for every admissible P | false | p is possible but false at root |
| ◇p ∧ ◇¬p | true | left and root respectively |

These witnesses refute `◇MC → MC` and `◇MC → □MC` in S4. No dead-end vacuity
is involved: every world has its self-loop. In fact the accessible left world
also has necessary full collapse by `MODAL-S4-LAWS`; even that stronger local
collapse does not remove root branching.

## Scope and extensionality

“All predicates” means all functions from this finite carrier to Prop, not a
finite sample. “Fixed language” means denotations of **all** modal formulas over
the two stipulated atoms, not the corpus's current inventory of statements.

In the paired model, right and twin agree on every fixed-language formula. Their
atomic valuations and successor rows coincide; structural induction handles all
formulas. Each has language-relative MC, but neither has full-predicate MC:
identity predicates distinguish the two accessible labels. Therefore the root's
`□◇MC` is false at full scope (right accesses no fully collapsed world), while
it is true at fixed-language scope (every successor has a language-collapsed
successor). In particular, S4 does not in general give `◇MC → □◇MC` either.

Optional world extensionality for the paired **language** is false: the distinct
right/twin labels agree on the entire language. This is stated, not hidden.
In the unpaired model the language separates every label: p identifies left,
the second atom identifies twin, and ◇p distinguishes root from right. World
extensionality for that language is proved, so imposing it does not rescue
`◇MC → MC` or `◇MC → □MC`. World extensionality for the all-predicate domain is
proved generally using identity predicates. It does not prohibit distinct
worlds that disagree on predicates.

## Proof and fidelity self-sweep

| Result | Accepted step and boundary |
|---|---|
| MODAL-S4-LAWS | K identity transport, reflexive converse and conditional symmetric transfer. No symmetry or terminality is smuggled into S4. |
| MODAL-S4-COUNTERMODELS | Exact finite edge tables, negated-atom refutation and independent true/false witnesses. Both domains and the common root stay explicit. |
| MODAL-S4-SCOPE-BOUNDARY | Formula induction explains restricted pair agreement; full identity predicates refute full collapse. The paired language explicitly fails extensionality. |
| MODAL-S4-EXTENSIONALITY | Three distinguishing formulas prove the unpaired language separates labels. Singleton-terminal witnesses prove its full `□◇MC`. |

The vocabulary records define S4, mutual-accessibility clusters, both pocket
models, the fixed language and independent p. Linked disambiguations distinguish
terminality, full collapse, language collapse and world extensionality, and keep
actual/possible/necessary collapse separate from possibility entails actuality.
No new source claim or frontier closure is advertised. All four Challenges were
frozen before proof search; Solutions preserve their types and permit no axioms.
