import TruthCore.Modal.NecessaryBeingMeasure

namespace TruthCore.Results.Modal.NecessaryBeingMeasure
open MeasureTheory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryBeingMeasure

/-- Almost-sure Euclidean/selected-reflexive validity equates the measures of
possible and actual bare NecessaryBeing, not actual existence or credence. -/
theorem measureEquality {Ω W B : Type} [MeasurableSpace Ω]
    (m : Ω → Ontic W B) (w : Ω → W) (μ : Measure Ω)
    (hValid : AlmostEverywhereModalValidity m w μ) : Equality m w μ := by
  sorry

end TruthCore.Results.Modal.NecessaryBeingMeasure
