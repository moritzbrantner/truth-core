import TruthCore.Modal.NecessaryBeingMeasure

namespace TruthCore.Results.Modal.NecessaryBeingMeasure
open MeasureTheory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryBeingMeasure
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

/-- Within THIS interpretation, transport the SAME c from an accessible world;
the reverse direction chooses the reflexively accessible selected standpoint. -/
theorem possible_iff_actual {Ω W B : Type} (m : Ω → Ontic W B) (w : Ω → W)
    (θ : Ω) (hEuclidean : TruthCore.Modal.Euclidean (m θ).frame)
    (hReflexive : ActualReflexive (m θ) (w θ)) :
    θ ∈ PossibleEvent m w ↔ θ ∈ ActualEvent m w := by
  constructor
  · rintro ⟨v, hwv, c, _hPresent, hNecessary⟩
    exact ⟨c, TruthCore.Causality.NonlimitingConcreteExistence.necessaryAtOrigin
      (m θ) (w θ) v c hEuclidean hReflexive hwv hNecessary⟩
  · intro hActual
    exact ⟨w θ, hReflexive, hActual⟩

/-- Almost-sure Euclidean/selected-reflexive validity equates the measures of
possible and actual bare NecessaryBeing, not actual existence or credence. -/
theorem measureEquality {Ω W B : Type} [MeasurableSpace Ω]
    (m : Ω → Ontic W B) (w : Ω → W) (μ : Measure Ω)
    (hValid : AlmostEverywhereModalValidity m w μ) : Equality m w μ := by
  apply measure_congr
  exact hValid.mono fun θ hθ => propext (possible_iff_actual m w θ hθ.1 hθ.2)

/-- Any SUPPLIED strict measure threshold is preserved. No threshold,
normalization, event measurability or credence interpretation is established. -/
theorem threshold {Ω W B : Type} [MeasurableSpace Ω]
    (m : Ω → Ontic W B) (w : Ω → W) (μ : Measure Ω)
    (hValid : AlmostEverywhereModalValidity m w μ) (q : ENNReal)
    (hThreshold : q < μ (PossibleEvent m w)) : q < μ (ActualEvent m w) := by
  have hEquality := measureEquality m w μ hValid
  exact hEquality ▸ hThreshold

end TruthCore.Results.Modal.NecessaryBeingMeasure
