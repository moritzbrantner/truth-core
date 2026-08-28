import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter6
namespace TruthCore.Results.Aristotle.Physics.ChangedThingPreviouslyChanging
open TruthCore.Greek.Aristotle.Physics
theorem changedThingPreviouslyChanging
    (ThingHasChanged CompletedChangeOccurredInTime ThingWasChangingEarlier : Prop)
    (hOccurred : CompletedChangeOccurredInTimeReading
      ThingHasChanged CompletedChangeOccurredInTime)
    (hPrior : DivisibleCompletionTimeYieldsPriorChangingReading
      CompletedChangeOccurredInTime ThingWasChangingEarlier) :
    ChangedThingWasPreviouslyChangingReading
      ThingHasChanged ThingWasChangingEarlier := by
  sorry
end TruthCore.Results.Aristotle.Physics.ChangedThingPreviouslyChanging
