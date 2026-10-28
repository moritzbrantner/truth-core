# Reading-only self-certification and regress adequacy

The task is specific: establish that an instrument's constant additive offset
is zero, uniformly over the stipulated model class. This is a deductive
model-class guarantee. It is not the task of obtaining a fallibly justified
belief, producing accurate predictions, or explaining why an instrument exists.

The new result is `SCIENCE-READING-SELF-CERTIFICATION`, bound to
`TruthCore.Results.Science.ReadingSelfCertification.certificate`. It composes
existing results rather than treating their conclusions as new assumptions:

- `TruthCore.Results.Science.MeasurementCalibration.certificate.1` gives the
  exact compensating-shift characterization of complete reading agreement.
- Its `.2.1` identifies the signal and bias when compared profiles share a
  supplied true signal value at a supplied input.
- `TruthCore.Results.Logic.CorrectionCriterion.characterization.1` characterizes
  exact data-relative classification by invariance on equal-data fibers.

`HistoryContrastive.Controls` already distinguishes discrimination from
sufficient ontological explanation. It does not establish this explicit
zero-offset target or the sound-positive-certificate obstruction. The present
result does not replace its explanatory vocabulary or strengthen its conclusion.

## The obstruction and its assumptions

A profile is `(f,b)`, where `f : X → V` is an unrestricted signal function and
`b : V` is one constant bias in an additive commutative group. Its complete
readings are `m(x)=f(x)+b`. Accuracy means `b=0` in this idealized profile.

For every profile and every permitted nonzero `d`, the profile
`(x ↦ f(x)+b−d, d)` has the same complete readings. This is supplied by the
existing compensating-shift theorem. Its bias is nonzero.

Fix any function `derive` from those complete readings to any evidence type,
and any positive test on that evidence. If the test uniformly guarantees zero
bias whenever it affirms, then it cannot affirm on the derived evidence of
**any** profile: the same affirmation would apply to the corresponding
nonzero-bias profile. The theorem assumes soundness only, not completeness.
An exact classifier fails as a further consequence, independently witnessed
using the existing criterion characterization.

The evidence type can be `Nat → Report`, or another type of report family.
Consequently, an infinite family derived solely from the same complete readings
cannot supply this uniform guarantee. This is an extensional statement about
information; it asserts no physical completion of infinitely many computations,
no finiteness of an agent, and no theorem that every infinite justification
chain is inadequate. A chain whose reasons introduce independent information
is outside the reading-only projection.

The input carrier may even be empty in the universal obstruction. The result
therefore does not infer an actual input from a universally quantified reading
condition. Its joint control uses two inhabited inputs and unequal readings:

| Profile | Signal at false/true | Constant bias | Complete readings |
| --- | --- | --- | --- |
| `p` | `0, 1` | `0` | `0, 1` |
| `q` | `−1, 0` | `1` | `0, 1` |

Both signals differ at both inputs; their true signal anchors at `false` are
`0` and `−1`. The witness rules out a vacuous constant-output reading of the
obstruction.

## The surviving case and strongest replies

Supplying the true signal value at one input, in addition to the complete
readings, admits an exact criterion under constant bias. The proof applies the
earlier calibration identification theorem and then the criterion equivalence.
The datum is genuinely the signal value in the formal definition; this proves
neither how an agent obtains it nor why a proposed calibration is trustworthy.
The earlier calibration result's input-dependent-bias control remains in force:
one anchor does not identify arbitrary variable bias.

Several substantive replies remain:

1. An instrument or theory may have justified, independently defended physical
   restrictions on signals or offsets. The compensating profile must remain
   admissible for this obstruction. A restricted class need not be closed under
   that shift; this theorem does not settle its identifiability.
2. A calibration channel, background theory or reason may bring information
   not derived solely from the same readings. Its reliability needs its own
   defense, but it is not excluded by the result.
3. A scientific account may seek empirical predictions or a convenient
   representative of the fitted class. Choosing zero bias as a representation
   convention is distinct from establishing that an unknown actual bias is zero.
4. An externalist or fallibilist theory need not require universally sound
   internal self-recognition for epistemic entitlement. The theorem does not
   establish that requirement. Related source work is recorded separately in
   PR #674; it is not a premise of this analyst theorem.
5. An infinitist can deny that its reasons are merely transformations of one
   evidence set, or deny that justification requires this deductive guarantee.
   Its positive adequacy account must be assessed on its actual commitments.

## Consequence for the regress investigation

This gives a bounded, concrete answer to what repeated self-support does not
show: unrestricted additive profiles remain observationally indistinguishable
with respect to the target zero bias, even after arbitrary reading-derived
reporting. It does not infer causal inactivity, nonexistence, a finite temporal
past, skepticism about all knowledge, or the falsity of all infinitism.

No new historical claim is made or attributed to Duhem, Wittgenstein, Goldman,
Vogel or Cohen. Existing source/context records prompted the analyst comparison;
the mathematical composition has independent identity. No new source witness
or historical source hunt is needed for it.

Actual root-path premise comparison: no premises added, removed or discharged.
All prior root-route open premises remain. The physical profile, the epistemic
norm appropriate to an actual self-certification claim, and the entitlement to
an independent anchor remain open philosophical/empirical questions.

## Verification boundary

The Challenge was frozen before the proof (SHA256
`56b0c2bc3fa9e7d52f205acb19e4d037e5e09378dd47ff210a6cb475f695225e`).
Focused combined-content diagnostics passed without errors at shared preview
`f2544a0142304bf074112e7323cb5b8ab6e46840`, content SHA256
`353aaefb5247a2ed251d573474548294d68ec58e19b694d6386ff4bf669b2aac`.
The content included the exact calibration declarations/proof from its pending
parent batch and used existing built imports; this is development evidence,
not canonical import/build certification. `#print axioms` reported `propext`
and `Quot.sound`, within the existing Mathlib policy. Final canonical build,
binding, Comparator and NanoDa belong to the delivered revision's CI.
