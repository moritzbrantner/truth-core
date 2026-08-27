import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter14

namespace TruthCore.Results.Aristotle.Physics.DistinctSimultaneousMotionsShareTime

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's shared-time argument in *Physics* IV.14, 223b1-13. -/
theorem distinctSimultaneousMotionsShareTime
    (MotionsAreDistinct TemporalNumbersAreEqual TemporalNumbersAreSimultaneous
      MotionsShareOneSameTime : Prop)
    (hNumbers :
      DistinctMotionsCanHaveEqualSimultaneousNumberReading
        MotionsAreDistinct TemporalNumbersAreEqual TemporalNumbersAreSimultaneous)
    (hTime :
      EqualSimultaneousNumberIsOneSameTimeReading
        TemporalNumbersAreEqual TemporalNumbersAreSimultaneous MotionsShareOneSameTime) :
    DistinctSimultaneousMotionsShareSameTimeReading
      MotionsAreDistinct MotionsShareOneSameTime := by
  sorry

end TruthCore.Results.Aristotle.Physics.DistinctSimultaneousMotionsShareTime
