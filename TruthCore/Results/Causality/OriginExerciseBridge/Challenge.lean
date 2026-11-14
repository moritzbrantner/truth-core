import TruthCore.Causality.OriginExerciseBridge
import TruthCore.Causality.ExistentialSelfActualization
import TruthCore.Results.Causality.ExistentialSelfActualization.Solution

namespace TruthCore.Results.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialSelfActualization

/-- If every origin-cause edge has an exercise of its source producing the
target's existence, an existing prohibition on productive self-actualization
excludes self-origin. This result has TWO explicit premises: the new bridge
and the independently recorded NoSelfProduction statement. That latter
statement already has a certified route from four open priority premises.
Nothing defines CausesOrigin as irreflexive. -/
theorem noSelfOriginFromNoSelfProduction {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F := by
  sorry

end TruthCore.Results.Causality.OriginExerciseBridge
