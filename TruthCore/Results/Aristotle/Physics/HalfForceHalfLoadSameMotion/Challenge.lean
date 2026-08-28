import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.HalfForceHalfLoadSameMotion
open TruthCore.Greek.Aristotle.Physics

theorem halfForceHalfLoadSameMotion
    (HalfForceAndHalfLoad ForceLoadRatioPreserved SameDistanceAndTime : Prop)
    (hRatio : HalfForceHalfLoadPreserveForceLoadRatioReading
      HalfForceAndHalfLoad ForceLoadRatioPreserved)
    (hMotion : PreservedForceLoadRatioEntailsSameDistanceTimeReading
      ForceLoadRatioPreserved SameDistanceAndTime) :
    HalfForceHalfLoadSameMotionReading
      HalfForceAndHalfLoad SameDistanceAndTime := by
  sorry

end TruthCore.Results.Aristotle.Physics.HalfForceHalfLoadSameMotion
