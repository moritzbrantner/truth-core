import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter6
namespace TruthCore.Results.Aristotle.Physics.MotionInEverySubinterval
open TruthCore.Greek.Aristotle.Physics
theorem motionInEverySubinterval
    (WholeTimeIsPrimary MovesInArbitrarySubinterval : Prop)
    (hCases : ArbitrarySubintervalMotionDichotomyReading
      MovesInArbitrarySubinterval)
    (hExcludes : NonmovingSubintervalExcludesPrimaryTimeReading
      MovesInArbitrarySubinterval WholeTimeIsPrimary) :
    MotionInEverySubintervalOfPrimaryTimeReading
      WholeTimeIsPrimary MovesInArbitrarySubinterval := by
  intro hPrimary
  rcases hCases with hMoves | hNotMoves
  · exact hMoves
  · exact False.elim (hExcludes hNotMoves hPrimary)
end TruthCore.Results.Aristotle.Physics.MotionInEverySubinterval
