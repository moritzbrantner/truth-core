module

public import TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork

/-- Same logical type as the preserved raw-form draft; named heads provide the exact corpus binding. -/
theorem namedRejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hNotV1 : NotV1GlobalDefinition F meaningful)
    (hTarget : V2ExcludedTarget F meaningful GlobalScope)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ChurchObservationSetting F)
    (hExcluded : ExcludedNegation meaningful) : NamedDemarcationFailure F meaningful := by
  exact TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection.namedRejection F meaningful hNotV1 hTarget hClosed hObservations hExcluded

end TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejectionBound
