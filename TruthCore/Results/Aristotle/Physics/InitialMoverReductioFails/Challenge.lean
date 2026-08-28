import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter1
namespace TruthCore.Results.Aristotle.Physics.InitialMoverReductioFails
open TruthCore.Greek.Aristotle.Physics
theorem initialMoverReductioFails
    (InitialReductioSucceeds
      InfiniteAggregateManySubjectsInFiniteTimeImpossible : Prop)
    (hRequires : InitialReductioRequiresAggregateImpossibilityReading
      InitialReductioSucceeds
      InfiniteAggregateManySubjectsInFiniteTimeImpossible)
    (hPossible : InfiniteAggregateManySubjectsInFiniteTimePossibleReading
      InfiniteAggregateManySubjectsInFiniteTimeImpossible) :
    InitialSimultaneousMotionReductioFailsReading
      InitialReductioSucceeds := by
  sorry
end TruthCore.Results.Aristotle.Physics.InitialMoverReductioFails
