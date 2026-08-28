import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10
namespace TruthCore.Results.Aristotle.Physics.IndivisibleCannotChangePerSe
open TruthCore.Greek.Aristotle.Physics
theorem indivisibleCannotChangePerSe
    (AtSource AtTarget SplitAcrossStates ChangeComplete Rests OngoingChange : Prop)
    (hCases : IndivisiblePrimaryChangeStateTrichotomyReading
      AtSource AtTarget SplitAcrossStates)
    (hNoSplit : IndivisibleExcludesSplitAcrossStatesReading SplitAcrossStates)
    (hTarget : TargetStateExcludesOngoingChangeReading
      AtTarget ChangeComplete OngoingChange)
    (hSource : SourceStateThroughIntervalExcludesChangeReading
      AtSource Rests OngoingChange) :
    IndivisibleCannotChangePerSeReading OngoingChange := by
  intro hChanging
  rcases hCases with hAtSource | hAtTarget | hSplit
  · exact hSource.2 (hSource.1 hAtSource) hChanging
  · exact hTarget.2 (hTarget.1 hAtTarget) hChanging
  · exact hNoSplit hSplit
end TruthCore.Results.Aristotle.Physics.IndivisibleCannotChangePerSe
