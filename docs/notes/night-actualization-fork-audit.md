# Night actualization: adversarial audit

This is the research evidence for
`ATTEMPT-NIGHT-ACTUALIZATION-FORK-AUDIT`, against baseline
`9bdac2abf1579d485fb3086482c3ccf8ac1b0d4c`.

## Conditional type acceptance

The existing `UnprecededPotencyActualizedReading` gives one `x,r` with
`InPotency x r`, `MovedIn x r`, and
`∀ y, InAct y r → ¬ PriorSimply y x`. The proposed frozen coverage statement
retains that same witness and concludes one of:

- `¬ ∃ y, MovesIn y x r ∧ InAct y r`;
- `MovesIn x x r ∧ InAct x r`;
- `∃ y, y ≠ x ∧ MovesIn y x r ∧ InAct y r ∧ ¬ PriorSimply y x`.

The conditional type and proposed Solution were independently inspected and
accepted: excluded middle splits actual-mover existence, then `y = x`. The
Night condition supplies the third branch's negative priority. Excluded
middle remains an explicit premise; this audit is not a checked proof.

`forcedOtherFromRootPremises` takes exactly Night, mover existence, mover
actuality, and act/potency non-simultaneity. Its positive third-branch proof is
constructive: choose a mover, obtain its actuality, exclude identity using the
selected potency, and apply the Night condition. No universal
moved-as-potency premise or independent inhabitation assumption is needed.
This makes explicit a positive boundary already present inside
`GenerationFromNightRefuted.coreFromRootPremises`; it does not defend those
root premises.

The proposed five-member root core adds the actual-mover/simple-priority
bridge. The third-branch mover then contradicts that bridge. This propagates
an existing conditional incompatibility into the configuration machinery;
it is not a newly discovered philosophical refutation. Inclusion-minimality
requires exact joint certificates for each deletion: omit Night (Residual),
mover existence (NoReduction), mover actuality (NonactualMover),
non-simultaneity (SelfMover), or priority bridge (OtherMover). The models
worker owns these certificates; this list is not their verification.

The completed core Solution was independently inspected: it applies the
existing `coreFromRootPremises` to all four listed commitments and then the
Night witness, exactly matching its frozen type. The models module and
registry extensions were also inspected: each of the five deletion masks
contains precisely the other four core members; OtherMover has an explicit
`jointRootBackground` conjunction; Overlap has `sameWitnessOverlap`; and
NonactualMover has a conjunction of no actual mover with an existing mover.
The record argument lists match those model predicates. No semantic/type
P1 was found. This inspection does not replace compilation or verification.

## Rejected readings and witness requirements

Coverage is not exclusivity. Both an actual self-mover and a distinct actual
mover can move the same witness. A proposed joint model uses `Bool` beings,
`Unit` respects, `false` moved and in potency, both beings in act, both moving
`false`, and nobody simply prior. Separate self/other models are not a joint
witness. The models worker must certify the overlap.

The first branch denies an **actual** mover in the given respect, not every
mover. The second uses same-respect `MovesIn x x r`, not Aristotle's
`SelfMovedIn` for a whole whose part moves another part; retain
`DISAMB-SELF-MOTION`. The third denies simple priority, not temporal priority,
and does not identify moving with efficient causation. Formal versus virtual
actuality remains the existing semantic-profile choice.

## Source evidence and correction

Ran `python3 scripts/source_evidence.py materialize ARIST-MET-XII-6` and read
the whole Greek chapter, 1071b3–1072a18. The consulted reading is
`ARIST-MET-1071B-NIGHT-GENERATION-A`, especially 1071b26–29. The text connects
Night and original-mixture cosmogonies to the aporia of potency's priority,
then asks how motion occurs without a cause in actuality. The existing claim
explicitly chooses simple priority and reads generation as reduction of
potency to act; source-integrity checks do not establish these choices.

At 1071b29–31 Aristotle denies matter's self-motion, with craft and generation
examples. This does not attribute the universal no-self-motion premise to
him. At 1072a3–8 he says potency's priority is in one way right and in another
wrong, and discusses whether chaos or Night existed for an infinite time.
Preserve the simple/temporal distinction. Hesiod and Orphic witnesses were
not read here; these are Aristotle's reported positions. The partition adds
no new attributed source reading.

Corrected `ATTEMPT-NIGHT-COSMOGONY-BUNDLE-ELIMINATION` in place: its old prose
treated Plato's self-moving soul (1071b37–1072a3) as affirming the
same-respect predicate and denying the corresponding no-self-motion premise.
That transfer requires a bridge not supplied by the report. Whole/parts
self-motion and `MovesIn x x r` remain distinct; the corrected record keeps
the existing proof and its historical search findings intact.

## Remaining limits and next discriminating test

The prior Night result already supplies three deletion interpretations and
an unactualized residual potency satisfying the bare rival. The new scope is
explicit coverage, a positive repair boundary, root-core propagation and
joint witnesses of the exact new assumptions. The residual remains untouched.

Adding Night to the Megarian motion core supplies motion but discriminates no
additional Night branch: the already sufficient motion/ability/incompleteness
core would merely be repackaged. Reject that as the next purported
constraint. A useful next test is whether proposed repairs of the Night
actual-mover/priority bridge preserve the independent motion commitments
jointly. This audit has checked no enlarged-bundle model.

No root premise closes. Exact-input Lean, binding, Comparator and NanoDa
verification remains required before the coordinator calls the results
certified.

## Integrated diff and moving survivor sweep

The integrated diff was independently reviewed against `9bdac2ab`, including
the fork/core Solutions and frozen Challenges, statement/argument/inference/
result prose, definition and disambiguation links, finite-model bindings and
the proposed `CONFIG-NIGHT-ACTUALIZATION`. The core and forced consequence
use constructive propositions; coverage's explicit excluded-middle premise
is excluded from configuration implication inputs. All five deletion masks
use one shared profile and each registered model satisfies the other four
commitments. These establish inclusion-minimality when their live gates
pass, not minimum cardinality. No source claim is added by the partition or
the model extensions.

One prose/type correction was requested and applied in the coordinator
checkout: remove “Under explicit excluded middle” from the fork statement's
paraphrase. The bound proposition is the existential fork itself; excluded
middle belongs to the coverage argument's premise list. With that correction,
the integrated scope inspected has no remaining semantic/type finding. Final
exact-input verification and frontier comparison remain delivery obligations.

The follow-on `TruthCore.Models.NightMovingResidual` and its registry record
`MODEL-NIGHT-MOVING-RESIDUAL` were also independently inspected. This one
three-being, one-respect interpretation satisfies the bare potency-priority
rival, all four root-core mover/actuality/non-simultaneity/priority commitments,
and present motion. Its `idle` potency has no prior actual being and is not
being moved at this evaluation. Its distinct `moved` potency is moved by the
actual `mover`, which is simply prior to it. All eight evaluations share that
one model: no separate residual and motion interpretations are joined.

`evaluation6` correctly composes the existing `coreFromRootPremises` theorem
to deny Night actualization; `evaluation7` uses `idle` to deny universal
act-priority. The three-constructor carrier enumeration and each registry
argument list match the model. No permanent-rest, smallest-carrier,
metaphysical-possibility or new source-attribution claim is made. This is a
genuine survivor of the specified background with present motion, not a
counterexample to a proved theorem or a defense of the rival's truth.

Audited source SHA256:
`e79baeec612ebef34575ff0f72e9d840423a11e88d949098f67df9264259e3c4`;
registry SHA256:
`eb953b9098ea0a35eb4d10e7ccf852782a64892ff8cd54c3200332fb57de19f9`.
The focused build/model-gate outcomes are owned by the proof worker and
coordinator; this paragraph records independent source/type/prose inspection.
The actual root-premise delta remains none.
