import TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V3RejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v3Rejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ChurchObservationSetting F)
    (hExcluded : ExcludedNegation meaningful) : NotV3GlobalDefinition F meaningful := by
  sorry
end TruthCore.Results.Logic.MeaningDefinitionFork.V3RejectionBound
