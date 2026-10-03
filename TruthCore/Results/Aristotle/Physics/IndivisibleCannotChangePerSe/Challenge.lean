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
  sorry
end TruthCore.Results.Aristotle.Physics.IndivisibleCannotChangePerSe
