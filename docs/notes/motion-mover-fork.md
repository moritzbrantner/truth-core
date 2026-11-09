# Scoped motion and mover fork

Target: `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER`, on the first-mover root route.
Analyst formulations; attribution deferred. The finite readings below are the
selected research scope. The original Physics VIII.4 attempt remains a failed
derivation of per-se coverage from the literal per-accidens division.

## Typed meanings and consequences

`TruthCore.Causality.MotionMoverFork` provides distinct inductive witness types:

- `BroadMotion`: the existing primitive reduction-from-potency-to-act witness.
- `PhysicalMotion`: that witness together with physical-respect classification.
- `SomeMover`: a per-se mover witness in the given respect, allowing self-links.
- `AnotherMoverAnyRespect`: the existing Physics VIII.5 distinct-mover witness
  in some respect. `AnotherMover` is its explicitly same-respect refinement.
- `AccidentalMover`: a witness of the separate per-accidens relation.

`MotionSense` and `MoverSense` select these meaning-bearing witness types. The
selection coverage and exclusivity statements are explicit open hypotheses for
a use's interpretation. Exclusivity means one constructor is selected, not that
extensions are disjoint. The batch proves universal branch coverage by cases,
which is stronger than a conclusion restricted to a selected constructor; it
therefore does not need to assume selection coverage or exclusivity.

The wrappers do not pretend to define the underlying metaphysical relations:
`MovedIn`, `MovesIn`, the physical classification and accidental moving retain
their existing primitive interpretations and open applicability obligations.
Heating is the physical example. An intellectual reduction is a stipulated
nonphysical framework example, not an independently established empirical case.
No transitivity, asymmetry, irreflexivity or well-foundedness is assumed here.

Physical motion entails broad reduction in this restricted interpretation;
the converse fails for a broad moved witness in a nonphysical respect. A
same-respect distinct mover entails a same-respect some mover. The respect-free
Physics VIII.5 reading entails only a mover in some respect. The joint mover
fork retains this weaker common conclusion: no unnoticed respect-alignment
assumption upgrades it to the prima via's same-respect mover premise.

The accidental branch supplies a per-se mover only under the explicit OPEN
`AccidentalHasPerSeMover` premise. It requires some per-se mover of the subject,
not that the accidental mover itself be per se. It does not identify the two
relations or derive per-se coverage from the literal Physics VIII.4 division.

## Root connection and exact scope

`broadFromPhysicalAndResidual` derives the existing root-route premise from:

1. Existing `STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER`.
2. `ResidualHasMover`: moved instances in an explicitly supplied residual class
   have per-se movers in the same respect.
3. `MotionCoverage`: every broad moved instance is physical or residual.

Unlike the existing all-reduction-is-physical route, this permits genuinely
nonphysical reductions. Both new premises remain OPEN. It is a new conditional
connection, not a discharge or independent defense of the mover principle.
Optional `MotionExclusive` excludes overlap between the two classes; the weakest
root proof does not need this extra assumption. The root theorem branches on
coverage, and `motionFork` establishes mover coverage for each typed motion sense.

The model controls exhibit both a physical and a residual moved instance with
movers and exclusive classes, so the joint bundle is nonvacuous. Removing each
of physical coverage, residual coverage or instance coverage permits a concrete
moved subject with no mover. The root implication could therefore have failed.

## Rivals and rejected identifications

The singleton self-link model satisfies 'some mover' but has no distinct mover.
It does **not** refute animal self-motion analyzed through distinct moving parts;
that interpretation needs an actual representation of the parts. The model
only separates the two quantified mover conditions.

An inertial state is not automatically a passage from potency to act. A model
of uniform motion without a sustaining mover challenges a premise only when
the selected motion predicate includes that state. No inertial-state/change
bridge is claimed here.

An accidental-only link with no per-se links refutes unconditional accidental
to per-se conversion. A nonphysical broad reduction with no mover satisfies
physical-only coverage vacuously but refutes broad coverage nonvacuously. These
preserve and refine the earlier preview findings; source attribution is deferred.

## Reproduction and remaining obligations

The seven result records are generated from `specs/motion-mover-fork.toml`.
The exploration map is `explorations/motion-mover-fork.toml`. The frozen Challenge
and Solution live under `TruthCore/Results/Causality/MotionMoverFork/`.
`controls` contains the finite witnesses and omission models.

The remaining philosophical obligations are the residual mover premise, instance
coverage and the accidental conversion premise; all remain open. A proposed
use of the respect-free mover theorem on the same-respect root route also needs
an explicit alignment bridge. No such alignment is silently supplied here.

## Bridge and dependency review

Review of PR #1253 at `2ef65375108f9db4900982afe08d43eeb7ddf191`
found that the same-respect refinement had incorrectly been registered as a
bridge from the broader Physics VIII.5 sense. The refinement theorem remains
true, but `AnotherMover moves x r` is stronger than the source sense's
`AnotherMoverAnyRespect moves x`. Its false bridge and the source-sense
definition link were removed. Stable sense UUIDs and labels are retained.

Every bridge in the batch was compared against its actual Lean interpretation:

| Registered result/premise | Source and destination scope |
| --- | --- |
| `anotherAnyGivesSomethingAny` conclusion | `AnotherMoverAnyRespect moves x → ∃ r, SomeMover moves x r`: the genuine respect-free sense bridge |
| `moverFork` conclusion | The `another` constructor has exactly `AnotherMoverAnyRespect moves x`; the result is `∃ q, SomeMover moves x q`, without alignment |
| `AccidentalHasPerSeMover` premise | `AccidentalMover accidental x r → SomeMover moves x r`; the open premise uses the exact two registered witness types |
| `physicalGivesBroad` conclusion | `PhysicalMotion physical moved x r → BroadMotion moved x r`; genuine typed forgetful projection |
| `broadFromPhysicalAndResidual` conclusion | A conditional adaptation of the existing raw-relation signature: physical-guard mover coverage, residual mover coverage and instance coverage together yield broad same-respect mover coverage |
| `motionFork` conclusion | Cases on exactly `BroadMotion` and `PhysicalMotion`, with the same three premises; the broad branch does not follow from physical coverage alone |

The bare `MotionCoverage` premise is not a type coercion between the two motion
witness types. Its previous bridge annotations were replaced by annotations on
the conditional conclusions, which retain the full support bundle. The existing
raw-signature root adapter remains distinguished from the genuinely typed
`physicalGivesBroad` projection. No Lean type, frozen Challenge, proof term,
control, or philosophical premise changed during this metadata repair.

The two bounded migration audits that pin `DISAMB-MOTION` were re-reviewed.
Its stable sense/definition identities and broad/physical distinction remain;
only the two witness declaration locators and appended scoped-fork explanation
changed. The audited old consumers still accept their supplied raw motion
predicates. They are not silently migrated to the new wrapper interpretations.
Their explicit First-Way existence disjunction, same-witness transports,
conditional attribute assembly and open naming/sufficiency assumptions remain.
The pinned audit dispositions now record this inspection instead of claiming
that the changed dependency was reused unchanged; their original before-state
and expression-contract baselines are preserved. The exact closures remain
70, 152 and 167 records, with unrelated results outside the reviewed scope.

## Part-mediated follow-up

The bounded `PartMediatedSelfMotion` batch targets
`STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT` on the first-mover route.
The existing typed Physics self-motion predicate leaves its internal anatomy
primitive. The existing `Vitalism` turnover profile and `ArrangementDynamics`
observation projection do not specify agent/patient roles in a motion event.
No existing theorem inspected supplies this populated projection comparison.

The finite carrier has a whole, a motor and a load; both components are proper
members of the whole. The only component event is motor moving load in the
respect displacement. Temperature supplies an explicit excluded respect.
`InternalMotion` contains actual members and an actual component event, rather
than an opaque animal-self-motion flag. A muscle moving a limb motivates the
example; biological adequacy and application of causal language remain OPEN.
The relation is an extensional stipulated event, not an empirical mechanics,
causal sufficiency claim, transitive causal order or temporal explanation.

The populated controls establish all of these together:

- The organism has internal motion and the load has a distinct component mover.
- The existing root no-self-motion predicate holds for the component relation.
- Patient-only lifting yields a motor-to-whole link in the same respect, with
  a mover distinct from the whole and no mover outside its proper parts.
- Raw component links supply no mover of the whole at all. Internal motion
  alone therefore does not justify whole mover coverage.
- Lifting both roles yields a whole-to-whole link; the existing root predicate
  fails for that aggregate relation while the whole is actually moved. This
  is an equivocation control, not a refutation of the component interpretation.
- Aggregate links also fail distinct whole-mover coverage: every aggregate
  agent is the whole. Membership does not preserve distinctness under this
  projection. Temperature is not silently substituted for displacement.

`localLift` derives `InternalHasDistinctMover moves` from the OPEN `LocalLift
moves`. The premise is restricted to actual internal events, rather than all
part motions, and retains the respect and agent. Proper membership supplies
agent/whole inequality. Its bundle is satisfiable: `PatientLift` realizes the
bridge by choosing the actual load. Omitting lifting has the populated
`ComponentMoves` countermodel; replacing patient lifting with aggregate
lifting has the populated `AggregateLift` countermodel. No external-agent
requirement follows: the satisfying patient-lift model has only an internal
motor as mover of its whole.

Root connection plan: compare the root's raw `MovesIn` interpretation with
these explicit projections. Unconditional transfer of component no-self-motion
to aggregate motion is rejected by `controls`. A universal root application
still needs a justified selection of the component/patient relation and
coverage of its relevant motion events; this finite model cannot supply
universal coverage or independent applicability. There is no root premise
truth discharge or anti-animal-self-motion conclusion. These two conditional
results are a bounded boundary analysis, not an isolated mereology library.

Claim/type sweep: `LocalLift` quantifies only over this finite carrier and its
actual internal events; `InternalHasDistinctMover` quantifies only over
`InternalMotion`. `Controls` is the conjunction for the named finite
interpretations, not a claim about all animals. `InternalMotion` is a distinct
inductive witness; `AnotherMover` and `SomeMover` retain their existing typed
meanings. No registered source sense is redefined, no source claim is added,
and the raw root predicate is instantiated explicitly in both component and
aggregate controls. The generated frozen Challenge retains those exact types.

Service experiment: the first Solution-only preview failed because the new
vocabulary is absent from the clean shared preview. Submitting the full
vocabulary and Solution together in `Scratch/partmotion/Combined.lean` succeeded
at preview HEAD `01f4ccd49052530e67e2d333b3de172ec75eabf2`, session
`pipeline-round-partmotion`, content SHA-256
`7046595b148f4eda3cb00d7ee1eab4f0f4038bcfb24f7e36e6ca59d4a8f92ec1`.
Repeated edit diagnostics worked with the lease and binding checks. Retain the
service for combined-source exploration; canonical module builds and final
Comparator/NanoDa checks remain necessary. This avoids modifying or rebuilding
the coordinator's preview for a new private vocabulary.

Verification: affected Solution/Challenge build, both result bindings and both
zero-axiom Comparator/NanoDa certificates pass. Corpus, generated records and
imports, module conversion, attribution and bounded bundle audits pass. The
computed frontier delta at base `83e3c8311` is unchanged: 379 open premises
(238 bare, 96 supported, 45 stated), 278 verified support alternatives and
lowest expanded route cost 28. The finite boundary analysis supplies no new
root-reaching support alternative. Final delivered-head CI remains required.
Shared conventions resolved at source revision
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
