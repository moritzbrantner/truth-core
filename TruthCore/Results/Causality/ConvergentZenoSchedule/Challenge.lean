import TruthCore.Causality.ConvergentSchedule

namespace TruthCore.Results.Causality.ConvergentZenoSchedule
open TruthCore.Causality

/-- The stage times `1 - (1/2)^n` form a strictly increasing real schedule
below `1` that converges to the endpoint time `1`, the stage durations
`(1/2)^(n+1)` telescope and sum to `1`, and the clock embeds the supertask
order `SupertaskPrecedes` into `<` on the reals. A mathematical model only; no
physical execution is asserted. -/
theorem convergentZenoSchedule : ConvergentZenoSchedule := by
  sorry

end TruthCore.Results.Causality.ConvergentZenoSchedule
