import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10
namespace TruthCore.Results.Aristotle.Physics.DivisibleTimeNoIndivisibleMotion
open TruthCore.Greek.Aristotle.Physics
theorem divisibleTimeNoIndivisibleMotion
    (EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      MotionInNow IndivisibleMoves SmallerThanIndivisible : Prop)
    (hTime : MotionOccursInDivisibleTimeReading
      EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion)
    (hNoNow : NothingMovesInNowReading MotionInNow)
    (hSmaller : DivisibleTimeMotionYieldsSmallerThanIndivisibleReading
      EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      MotionInNow IndivisibleMoves SmallerThanIndivisible)
    (hImpossible : IndivisibilityExcludesSmallerTraversalReading
      SmallerThanIndivisible) :
    NoIndivisibleCanMovePerSeReading IndivisibleMoves := by
  sorry
end TruthCore.Results.Aristotle.Physics.DivisibleTimeNoIndivisibleMotion
