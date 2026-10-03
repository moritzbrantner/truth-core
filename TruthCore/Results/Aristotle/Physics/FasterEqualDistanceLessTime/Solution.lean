import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter2

namespace TruthCore.Results.Aristotle.Physics.FasterEqualDistanceLessTime

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's trichotomy proof in *Physics* VI.2, 232b12-20. -/
theorem fasterEqualDistanceLessTime
    (EqualTime LessTime GreaterTime : Prop)
    (hTrichotomy :
      EqualDistanceTimeComparisonTrichotomyReading EqualTime LessTime GreaterTime)
    (hExclusions :
      FasterExcludesEqualOrGreaterTimeForEqualDistanceReading EqualTime GreaterTime) :
    FasterTraversesEqualDistanceInLessTimeReading LessTime := by
  rcases hTrichotomy with hEqual | hLess | hGreater
  · exact False.elim (hExclusions.1 hEqual)
  · exact hLess
  · exact False.elim (hExclusions.2 hGreater)

end TruthCore.Results.Aristotle.Physics.FasterEqualDistanceLessTime
