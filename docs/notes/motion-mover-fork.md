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
