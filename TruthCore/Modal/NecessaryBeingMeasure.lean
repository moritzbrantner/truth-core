import TruthCore.Causality.NonlimitingConcreteExistence
import Mathlib.MeasureTheory.Measure.Basic

/-!
Analyst measure consumer over interpretations, not a causal-default theory or
an attributed formalization of A10. Each interpretation has its own Ontic and
selected standpoint. The events use the existing bare NecessaryBeing: present
existence of an individual necessary relative to the supplied accessibility.
No causal capability, concreteness, God identity or global witness is added.
-/
namespace TruthCore.Modal.NecessaryBeingMeasure
open MeasureTheory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

/-- Interpretations at which a bare necessary being exists at an accessible
world. The individual witness may differ between interpretations. -/
def PossibleEvent {Ω W B : Type} (m : Ω → Ontic W B) (w : Ω → W) : Set Ω :=
  fun θ => ∃ v, (m θ).frame.access (w θ) v ∧ NecessaryBeing (m θ) v

/-- Interpretations with a bare necessary being at their selected standpoint.
Actual here is internal to each interpretation, not asserted reality. -/
def ActualEvent {Ω W B : Type} (m : Ω → Ontic W B) (w : Ω → W) : Set Ω :=
  fun θ => NecessaryBeing (m θ) (w θ)

/-- OPEN support condition: almost every interpretation has a Euclidean frame
and reflexivity at its selected standpoint. This asserts no probable existence,
metaphysical applicability, uniform prior or normalization. -/
def AlmostEverywhereModalValidity {Ω W B : Type} [MeasurableSpace Ω]
    (m : Ω → Ontic W B) (w : Ω → W) (μ : Measure Ω) : Prop :=
  ∀ᵐ θ ∂μ, Euclidean (m θ).frame ∧ ActualReflexive (m θ) (w θ)

/-- Equality of arbitrary measures of the two events, not their truth or a
probability estimate. For arbitrary sets these may be outer-measure values. Probability
interpretation separately requires measurable events, a normalized measure and
coherent semantic-event modeling; none is needed for this equality. -/
def Equality {Ω W B : Type} [MeasurableSpace Ω]
    (m : Ω → Ontic W B) (w : Ω → W) (μ : Measure Ω) : Prop :=
  μ (PossibleEvent m w) = μ (ActualEvent m w)

end TruthCore.Modal.NecessaryBeingMeasure
