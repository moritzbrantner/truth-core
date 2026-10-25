import TruthCore.Causality.LocalTransmission

namespace TruthCore.Results.Causality.LocalObservationSelectsSolution
open TruthCore.Causality

/-- A fixed observation at index zero propagates upstream by ordinary Nat
induction in both directions. The model is mathematically determined once
the datum is supplied, though the datum still needs causal explanation. -/
theorem localObservationSelectsSolution : LocalObservationSelectsSolution := by
  intro active hTransmission
  constructor
  · intro hZero n
    induction n with
    | zero => exact hZero
    | succ n ih => exact (hTransmission n).mp ih
  · intro hZero n
    induction n with
    | zero => exact hZero
    | succ n ih =>
      intro hNext
      exact ih ((hTransmission n).mpr hNext)

end TruthCore.Results.Causality.LocalObservationSelectsSolution
