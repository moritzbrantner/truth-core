import TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem namedRejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hNotV1 : NotV1GlobalDefinition F meaningful)
    (hTarget : V2ExcludedTarget F meaningful GlobalScope)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ChurchObservationSetting F)
    (hExcluded : ExcludedNegation meaningful) : NamedDemarcationFailure F meaningful := by
  sorry
end TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejectionBound
