import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter3

namespace TruthCore.Results.Aristotle.Physics.NothingMovesInNow
open TruthCore.Greek.Aristotle.Physics
/-- Aristotle's motion reductio in *Physics* VI.3, 234a24-31. -/
theorem nothingMovesInNow (MotionInNow PrimaryNowDivisible : Prop)
    (hNotDivisible : PrimaryNowNotDivisibleReading PrimaryNowDivisible)
    (hMotionDivides : MotionInNowImpliesNowDivisibleReading MotionInNow PrimaryNowDivisible) :
    NothingMovesInNowReading MotionInNow := by
  intro hMotion
  exact hNotDivisible (hMotionDivides hMotion)
end TruthCore.Results.Aristotle.Physics.NothingMovesInNow
