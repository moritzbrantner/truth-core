import TruthCore.Alternatives.McTaggart

/-!
McTaggart's position on change as a theory bundle (#497), not his whole
metaphysics. It is the strongest sourced rival behind the unattributed
McTaggart-style rival `ChangeUnrealButAppearsReading` of the prima via's
observation premise `SomethingIsMovedReading`.

Both commitments are sourced to the pinned 1908 paper (claims
`MCTAGGART-1908-TIME-UNREAL-A`, `MCTAGGART-1908-ALL-CHANGE-A-SERIES-A`). The
C series, the direction of time and McTaggart's later answer to the retorsion
(*The Nature of Existence* II, ch. XLIV, § 511, read as
`TruthCore.Alternatives.McTaggart.AppearingsDoNotChangeReading`) are not part
of this bundle.
-/

namespace TruthCore.Comparison.McTaggart

open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart

universe u

/-- McTaggart 1908 on change: no event changes in its A-series determinations,
yet there are judgings and perceivings; and all change is A-series change. -/
def UnrealityOfTime {Being : Sort u}
    (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
    (Changes : Being → Prop) : Prop :=
  NoASeriesChangeButAppearsReading ASeriesChanges Opines ∧
    AllChangeIsASeriesChangeReading Changes ASeriesChanges

end TruthCore.Comparison.McTaggart

namespace TruthCore.Alternatives.McTaggart

/-- Conclusion of the elimination: McTaggart's bundle on change does not hold
(for the given interpretation of its vocabulary). Kept outside
`TruthCore.Comparison` because it is a refutation, not a theory. -/
def UnrealityOfTimeFalse {Being : Sort u}
    (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
    (Changes : Being → Prop) : Prop :=
  ¬ TruthCore.Comparison.McTaggart.UnrealityOfTime ASeriesChanges Opines Changes

end TruthCore.Alternatives.McTaggart
