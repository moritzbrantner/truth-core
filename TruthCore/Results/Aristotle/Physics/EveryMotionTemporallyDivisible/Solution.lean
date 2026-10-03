import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter4

namespace TruthCore.Results.Aristotle.Physics.EveryMotionTemporallyDivisible
open TruthCore.Greek.Aristotle.Physics
/-- Aristotle's temporal-divisibility argument in *Physics* VI.4, 235a10-13. -/
theorem everyMotionTemporallyDivisible
    (EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      EveryMotionTemporallyDivisible : Prop)
    (hPremises : MotionOccursInDivisibleTimeReading EveryMotionOccursInTime
      EveryTimeDivisible SmallerTimeHasSmallerMotion)
    (hTransition : DivisibleTimeImpliesMotionTemporallyDivisibleReading
      EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      EveryMotionTemporallyDivisible) :
    EveryMotionTemporallyDivisibleReading EveryMotionTemporallyDivisible := by
  exact hTransition hPremises
end TruthCore.Results.Aristotle.Physics.EveryMotionTemporallyDivisible
