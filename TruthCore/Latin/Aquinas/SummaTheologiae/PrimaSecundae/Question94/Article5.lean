/-! One reading of the alternative explanation in ST I-II q.94 a.5 ad 1.
The witness is AQUINAS-ST-I-II-Q94-A5, SCTA Leonine TEI. -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

/-- In some hearts, in some respects, people thought good what is naturally
evil, and this corruption needed correction. `φ` names the matter judged;
`BelievesGood x φ` is that person's affirmative evaluation, not its truth.

This is the second of the source's alternative explanations of the written
law's corrective role. It asserts need, not an accomplished correction, a
chronology, or a general theory of moral improvement. -/
def CorruptedNaturalLawNeedsCorrectionReading {Agent Matter : Type}
    (BelievesGood : Agent → Matter → Prop) (NaturallyEvil : Matter → Prop)
    (NeedsCorrection : Agent → Matter → Prop) : Prop :=
  ∃ x φ, BelievesGood x φ ∧ NaturallyEvil φ ∧ NeedsCorrection x φ

end TruthCore.Latin.Aquinas.SummaTheologiae
