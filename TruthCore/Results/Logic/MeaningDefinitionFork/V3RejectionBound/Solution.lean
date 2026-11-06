module

public import TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V3RejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork

/-- Same logical type as the preserved raw-form draft; named heads provide the exact corpus binding. -/
theorem v3Rejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ChurchObservationSetting F)
    (hExcluded : ExcludedNegation meaningful) : NotV3GlobalDefinition F meaningful := by
  exact TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection.v3Rejection F meaningful hClosed hObservations hExcluded

end TruthCore.Results.Logic.MeaningDefinitionFork.V3RejectionBound
