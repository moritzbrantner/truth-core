module

public import TruthCore.Causality.EternityDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EternityDefinitions.PrimitiveComposition
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.EternityDefinitionFork

/-- Frozen analyst consequence; no semantic calibration or actual-life premise adopted. -/
theorem primitiveComposition (f : Frame)
    (hSuccession : SuccessionRequiresPotencyReading f.InPotency f.LivesAt f.lifeStateAt)
    (hBoundary : LifeBoundaryRequiresPotencyReading f.InPotency f.LivesAt)
    (hLife : PureActLivesReading f.InPotency f.LivesAt)
    (hRecognition : BoethianRecognition f) :
    ImmutableIsEternalReading f.InPotency f.Eternal := by
  have hTyped := TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal.immutableIsBoethianEternal
    f.InPotency f.LivesAt f.lifeStateAt hSuccession hBoundary hLife
  intro x hx
  exact hRecognition x (hTyped x hx)

end TruthCore.Results.Causality.EternityDefinitions.PrimitiveComposition
