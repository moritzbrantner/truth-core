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
  intro hValid
  exact hFalse (hDepends hValid)
end TruthCore.Results.Aristotle.Physics.StadiumInferenceInvalid
