import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter9
namespace TruthCore.Results.Aristotle.Physics.StadiumInferenceInvalid
open TruthCore.Greek.Aristotle.Physics
theorem stadiumInferenceInvalid
    (StadiumInferenceValid MovingAndStationaryComparisonsTakeEqualTime : Prop)
    (hDepends : StadiumInferenceDependsOnMovingStationaryEqualTimeReading
      StadiumInferenceValid MovingAndStationaryComparisonsTakeEqualTime)
    (hFalse : MovingStationaryEqualTimePremiseFalseReading
      MovingAndStationaryComparisonsTakeEqualTime) :
    StadiumInferenceInvalidReading StadiumInferenceValid := by
  sorry
end TruthCore.Results.Aristotle.Physics.StadiumInferenceInvalid
