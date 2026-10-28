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
