# Necessary bearer and causal capacity (#435, target 3)

`NECESSARY-CONCRETE-CAUSAL-CAPACITY` checks one response-function theory in
which a literal individual exists necessarily and meets a causal-capacity
criterion of concreteness. It establishes **formal satisfiability of this
specified theory**. It supplies no evidence that the worlds are metaphysically
possible, that the bearer actually exists, or that necessary existence explains
itself. The conclusion is not a duplicate of #445's quantifier countermodels.

## Verified source assessment

The pinned witness `SEP-ABSTRACT-OBJECTS-2020-CRITERIA` is Gideon Rosen,
[“Abstract Objects,” Fall 2020 archive](https://plato.stanford.edu/archives/fall2020/entries/abstract-objects/),
materialized and read before modeling. Sections 3.1–3.2 distinguish spatial
criteria from causal inefficacy. Section 3.2 presents the causal criterion but
raises epiphenomenal qualia and created abstract artifacts against simple
biconditionals. Its final paragraph identifies a further problem: explaining
which participation in causal events gives an object causal efficacy. This
leaves a substantive rival objection to any response-function proxy.

This is the author's assessment of surveyed criteria, not a primary witness
for every surveyed ontology. It supplies neither a contingency axiom for all
power bearers nor the intervention signature below. We reject attributing
that signature to Rosen, equating his critical survey with an endorsement,
and labeling every causally idle recipient abstract. No new historical claim
is extracted from it. The archived assessment is not asserted to be the latest
revision.

## Exact analyst commitments

`Response W I := I → I → W → Bool → Bool` represents the recipient's output
under activating or deactivating a particular bearer. These interventions are
stipulated causal inputs: mere observed correlation would not justify that
interpretation. There is no extra modal engine. `Frame`, `Box`, `ExistsAt`,
`ConcreteAt`, and literal identity are exactly those of #261/#445.

`Capacity F ex r x w` requires an accessible `v` and distinct `y` such that
both endpoints exist at `v` and activation changes the recipient output there.
This is a manifestation-based capacity criterion, not a definition of all
metaphysical causation. `Disciplined` independently checks that deactivation
never produces output and positive activated output has distinct existing
endpoints. Neither definition asserts a necessary individual. The existence
extension, response function and accessibility relation are separate inputs.

The criterion supplied to `ConcreteAt` is this `Capacity`, so present concrete
existence is `ex x w ∧ Capacity F ex r x w`. Abstractness is not defined.
Neither spatiotemporal location nor ontological independence is encoded.

## Complete finite model and controls

Both worlds and the fixed roster are `Bool`, with universal accessibility.
Actual world is `false`; accessible `true` is distinct, and reflexivity is
checked. The bearer `false` exists at both worlds. Recipient `true` exists
only at `true`. Identity is literal Lean equality across worlds, not counterpart
identity. Actualist quantification uses the explicit existence extension.

The response table is `(!x) && y && w && on`:

| World | Bearer | Recipient | Deactivated output | Activated output |
| --- | --- | --- | --- | --- |
| false | false | true | false | false |
| true | false | true | false | true |
| either | every other pair | | false | false |

At the actual world every response is dormant. Nevertheless the necessary
bearer has capacity there because `true` is accessible; it has capacity at
`true` too. The same bearer is therefore necessarily concrete under this
criterion. The proof reuses `deRe_to_deDicto`, rather than restating its
conclusion as a premise, to obtain necessary concrete exemplification.
The contingent recipient distinguishes this from a model in which every
existence fact is necessary. Keeping existence and accessibility fixed while
replacing all responses by `false` removes every capacity. Thus necessary
existence alone does not force the capacity result. These are omission and
nonvacuity controls, not a claim that an inconsistent rival theory was found.

## Strong surviving rival and remaining obligations

A causal-powers realist can require an intrinsic, directed power, with a
substantive account of causal production and participation in events. That
requirement is not met merely by an accessible intervention-output difference.
The current signature tests a clear capacity theory with independent response
discipline; it does **not** establish that it is the strongest possible causal
ontology or defeat the intrinsic-power rival. Turning that objection into a
further formal target requires a sourced account of intrinsic directedness and
its connection to the current causal vocabularies, rather than inserting an
axiom that all powers are contingent. The signature is a stipulated diagnostic,
not a sourced solution to that modeling problem. The recipient's lack of
outgoing power is an additional reason not to infer an abstract/concrete
partition from it.

A naturalist may accept a necessary powered physical bearer or may reject
necessary concrete existence using additional defended premises. Monism may
instead dispute the distinct-recipient representation. This result settles
neither dispute; necessity alone makes no prediction about the activation
input or recipient's contingent existence. No assertion that all naturalism
or monism is refuted is warranted.

Issue #435 remains open for the intrinsic-power refinement, separately sourced
spatiotemporal and independence/actuality criteria, abstract-object distinctions,
and varying-domain/counterpart alternatives. Necessary existence, underived
actuality, uncausedness and explanatory adequacy remain separate questions.
No root-path open premise is removed or added; the earlier collective
possibility bridge stays open. The attempt records a successful diagnostic,
not closure of a philosophical frontier obligation.

## Prose/type audit

All statement, inference, argument and result prose uses exactly the conjuncts
of `CausalPowers.Compatibility`: reflexivity and distinct accessible world;
response discipline; actual and boxed existence of `false`; boxed capacity of
that same `false`; necessary concrete exemplification; dormancy at `false`;
activation-sensitive manifestation at `true`; recipient absence/presence; and
the zero-response control. The theorem is parameter-free, asserting these
specific tables; there are no unlisted philosophical hypotheses. Definitions
and disambiguations distinguish generic capacity, this response criterion,
actual transmission, generic concrete presence, and the earlier modal scopes.
