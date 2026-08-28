import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10
namespace TruthCore.Results.Aristotle.Physics.NoIndeterminateChange
open TruthCore.Greek.Aristotle.Physics
theorem noIndeterminateChange
    (EveryChangeFromSourceToTerminus ActualEndpointPossible
      InfiniteExtentTraversable ChangeLacksDeterminateTermini : Prop)
    (hFromTo : EveryChangeFromSomethingToSomethingReading
      EveryChangeFromSourceToTerminus)
    (hPossible : ActualChangeEndpointMustBePossibleReading
      ActualEndpointPossible)
    (hUntraversable : InfiniteExtentCannotBeTraversedReading
      InfiniteExtentTraversable)
    (hTransition : ChangeTerminusPremisesExcludeIndeterminateInfinityReading
      EveryChangeFromSourceToTerminus ActualEndpointPossible
      InfiniteExtentTraversable ChangeLacksDeterminateTermini) :
    NoChangeInfiniteThroughIndeterminateTerminiReading
      ChangeLacksDeterminateTermini := by
  exact hTransition hFromTo hPossible hUntraversable
end TruthCore.Results.Aristotle.Physics.NoIndeterminateChange
