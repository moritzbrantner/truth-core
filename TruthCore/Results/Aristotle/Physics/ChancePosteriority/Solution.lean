import TruthCore.Greek.Aristotle.Physics.BookII.Chapter6

namespace TruthCore.Results.Aristotle.Physics.ChancePosteriority

open TruthCore.Greek.Aristotle.Physics

/-- Incidental causal status makes chance and spontaneity posterior to mind and nature. -/
theorem chanceSpontaneityPosteriorToMindNature
    (ChanceSpontaneityBelongToSourceOfMotionMode
      ChanceSpontaneityAreIncidentalCauses
      NatureOrThoughtCouldProperlyCauseTheirOutcomes
      TheirIncidentalCausesAreIndefinite
      NoIncidentalCausePriorToProperCause
      ChanceSpontaneityPosteriorToMindAndNature
      CosmicSpontaneityWouldNotDisplacePriorMindNature : Prop)
    (hClassification :
      ChanceSpontaneityEfficientIncidentalCausesReading
        ChanceSpontaneityBelongToSourceOfMotionMode
        ChanceSpontaneityAreIncidentalCauses
        NatureOrThoughtCouldProperlyCauseTheirOutcomes
        TheirIncidentalCausesAreIndefinite)
    (hBridge :
      IncidentalPriorityImpliesChancePosteriorityReading
        ChanceSpontaneityAreIncidentalCauses
        NatureOrThoughtCouldProperlyCauseTheirOutcomes
        NoIncidentalCausePriorToProperCause
        ChanceSpontaneityPosteriorToMindAndNature
        CosmicSpontaneityWouldNotDisplacePriorMindNature) :
    ChanceSpontaneityPosteriorMindNatureReading
      ChanceSpontaneityPosteriorToMindAndNature
      CosmicSpontaneityWouldNotDisplacePriorMindNature := by
  exact hBridge.2 ⟨hClassification.2.1, hClassification.2.2.1⟩

end TruthCore.Results.Aristotle.Physics.ChancePosteriority
