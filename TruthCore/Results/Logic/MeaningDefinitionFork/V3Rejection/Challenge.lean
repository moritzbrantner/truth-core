import TruthCore.Logic.MeaningDefinitionFork
import TruthCore.Results.Logic.Verificationism.Ayer1946Closure.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v3Rejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃)
    (hExcluded : ExcludedNegation meaningful) : ¬ V3Definition F meaningful GlobalScope := by
  sorry

end TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection
