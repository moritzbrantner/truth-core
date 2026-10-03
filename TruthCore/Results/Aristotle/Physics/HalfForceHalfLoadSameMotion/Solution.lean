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
  intro hHalves
  exact hMotion (hRatio hHalves)

end TruthCore.Results.Aristotle.Physics.HalfForceHalfLoadSameMotion
