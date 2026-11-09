import TruthCore.Causality.PartMediatedSelfMotion

namespace TruthCore.Results.Causality.PartMediatedSelfMotion
open TruthCore.Causality.PartMediatedSelfMotion
open TruthCore.Causality.MotionMoverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem localLift (moves : Carrier → Carrier → Respect → Prop)
    (h : LocalLift moves) : InternalHasDistinctMover moves := by
  sorry

theorem controls : TruthCore.Causality.PartMediatedSelfMotion.Controls := by
  sorry
end TruthCore.Results.Causality.PartMediatedSelfMotion
