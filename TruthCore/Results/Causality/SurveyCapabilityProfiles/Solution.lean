module
public import TruthCore.Causality.SurveyCapabilityProfiles
@[expose] public section
namespace TruthCore.Results.Causality.SurveyCapabilityProfiles
open TruthCore.Causality.SurveyCapabilityProfiles

theorem profiles : Certificate := by
  exact ⟨fun _ => outgoingIncident, fun _ _ _ => dispositionExercise,
    fun _ _ _ => exerciseDisposition, fun _ => denialTransfer,
    exerciseSeparator, dispositionSeparator, unexercisedDisposition,
    omitRealization, omitAttribution, bothBridges, denialSeparators⟩
end TruthCore.Results.Causality.SurveyCapabilityProfiles
