import TruthCore.Logic.MeaningDefinitionFork
import TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection.Solution
import TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem namedRejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hNotV1 : ¬ V1Definition F meaningful GlobalScope)
    (hTarget : V2ExcludedTarget F meaningful GlobalScope)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃)
    (hExcluded : ExcludedNegation meaningful) : NamedDemarcationFailure F meaningful := by
  sorry

end TruthCore.Results.Logic.MeaningDefinitionFork.NamedRejection
