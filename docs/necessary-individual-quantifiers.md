# Necessary individuals and the quantifier shift

This is the first mathematical control for #435. It leaves that issue open.
It adds no attributed philosophical reading and no evidence that a necessary
concrete individual actually exists or is metaphysically possible.

## Fixed roster and two distinct predicates

The module imports the existing modal fixture (#261), its shared `Frame`,
`Box` and `Dia`, and the actualist embedding's `ExistsAt`. It adds no modal
engine. Individuals form a fixed possibilist roster `I`; a variable denotes the
same Lean individual across worlds. Literal equality is used, not a counterpart
relation. World-dependent `ex x w` determines the actualist extension. An
actualist outer existential is `∃ x, ex x w ∧ …`, as one law explicitly shows.
No theorem here covers an ontology with varying outer rosters or counterparts.

`ConcreteAt ex concrete x w := ex x w ∧ concrete x w`. The supplied criterion
`concrete` is theory-relative. It is not a defended account of causal powers,
spatiotemporal location or independence/actuality. An absent concrete extension
does not establish the presence or absence of abstract objects.

| Proposition | Exact formal scope |
| --- | --- |
| `DeRe F ex w` | `∃ x, Box F (ex x) w` |
| `DeDicto F (ConcreteAt ex concrete) w` | `Box F (fun v => ∃ x, ex x v ∧ concrete x v) w` |
| `IndividualContingency F ex w` | `∀ x, Dia F (fun v => ¬ ex x v) w` |
| `JointAbsence F (ConcreteAt ex concrete) w` | `Dia F (fun v => ¬ ∃ x, ex x v ∧ concrete x v) w` |

The actual world `w` is supplied explicitly, so the world type is inhabited
whenever a law is instantiated. The conditional laws need no reflexivity;
therefore a boxed property alone does not carry an implicit actuality claim.
The finite controls instead use actual world `false` and universal accessibility,
with explicit access to `true`, distinctness, and reflexivity in the alternating
contract. Empty extensions are evaluated at elements of `Bool`, never by setting
`World := Empty`.

## What follows and what fails

`NECESSARY-INDIVIDUAL-LAWS` proves that a fixed necessary witness gives a witness
at every successor, and that joint absence gives absence of each fixed member.
It also retains an explicit actualist outer witness in a separate variant.
To pass from necessary existence to necessary concrete exemplification, the
law requires `∀ v, F.access w v → ∀ x, ex x v → concrete x v`. This is the exact
additional existence-to-concreteness premise used by that law, not a conclusion
from the meaning of necessity.

`NECESSARY-INDIVIDUAL-ALTERNATING` checks this entire finite table:

| Rigid individual | World `false` | World `true` |
| --- | --- | --- |
| `false` | exists and concrete | absent |
| `true` | absent | exists and concrete |

Both worlds are accessible from either world. Every individual is absent
somewhere, but no accessible world is concretely empty. Every world has a
concrete witness, but no fixed individual exists at both. Thus neither the
individual-to-joint absence direction nor the de-dicto-to-de-re direction is
valid over these stated fixed-roster semantics. The converse directions proved
in `Laws` are constructive and have no extra classical axiom.

`NECESSARY-INDIVIDUAL-CONCRETE-BRIDGE` uses that same world type and accessibility,
but makes existence true and the concrete criterion false everywhere. A fixed
individual exists necessarily while concrete exemplification fails and an
accessible world has an empty concrete extension. This witnesses the need for
the additional concreteness bridge within the supplied theory-relative model.
It does not defend an ontology allowing such a criterion.

### Contingent exercise of causation

`TruthCore/Modal/NecessaryContingentActivity.lean` adds a small source-free
model test using the already defined Kantian `Ontic` relation. The individual
`false` exists in both universally accessible worlds. At the first world it
causes the distinct, existing individual `true`; at the other world it causes
nothing. Every stipulated causal arrow has an existing cause and effect.
`necessaryWithContingentActivity` proves these conditions jointly satisfiable.

This separates **necessary existence** from **necessary exercise of causation**.
It does not identify causal activity with an enduring *power*, establish that
the bearer is concrete under any theory of concreteness, or demonstrate the
metaphysical possibility of the model. The powers, location and independence
criteria in #435 remain open research questions.

## Relationship to the Third Way and remaining work

`collective_iff` substitutes `fun P => Dia F P w` for the primitive `Possible`
in the existing `AllCanNotBeThenNothingPossibleReading`. Under that explicit
formal instantiation its type is equivalent to individual contingency implying
joint absence. The alternating control falsifies that instantiated formula.
This neither identifies possible worlds with temporal instants nor refutes the
Third Way's source-attributed premise about the actual universe. It does not
reproduce the temporal plenitude argument or its infinite-past hypothesis.
The existing integer relay model and its source records remain distinct.

Scott's essence-based necessary existence (#274), the Third Way's cannot-not-be,
and a fixed bearer's Kripke-boxed presence are separate notions. No converse
between them is asserted. Like the constructive existence comparison (#275),
this control separates quantifier consequences from an actuality assertion;
it does not replace those existing results with a new existence doctrine.

Intended and actual root-path open-premise change: none. The existing collective
possibility premise remains open. The new results establish mathematical laws
and finite-model properties only; they add no argument concluding that premise
or a necessary concrete individual. Strong rival accounts of concreteness,
pinned source defenses, genuinely varying-domain/counterpart alternatives, and
separate treatment of abstract-object extensions remain work for #435.
