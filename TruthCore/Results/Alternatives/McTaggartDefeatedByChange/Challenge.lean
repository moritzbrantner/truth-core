import TruthCore.Comparison.McTaggart
import TruthCore.Observation.Change
namespace TruthCore.Results.Alternatives.McTaggartDefeatedByChange
open TruthCore.Alternatives.McTaggart
open TruthCore.Observation.Change

/-- McTaggart's bundle on change is defeated by consequence against F3. -/
theorem bundleDefeatedByChange {Being : Type}
    (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
    (Changes : Being → Prop)
    (hChange : SomethingChangesReading Changes) :
    UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  sorry

/-- F3 is needed: where one being opines and nothing changes, McTaggart's
bundle holds. -/
theorem needsSomethingChanges :
    ¬ ∀ (Being : Type) (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
        (Changes : Being → Prop),
      UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  sorry
end TruthCore.Results.Alternatives.McTaggartDefeatedByChange
