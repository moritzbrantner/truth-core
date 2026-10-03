import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter10

namespace TruthCore.Results.Aristotle.Physics.TimeIsNotMotion

open TruthCore.Greek.Aristotle.Physics

/-- Motion is local to its changing subject while time is universal, so time is not motion. -/
theorem timeIsNotMotion
    (EachMotionIsLocalToChangingSubject TimeIsEverywhereAlike TimeIsMotion : Prop)
    (hScope :
      MotionLocalWhileTimeUniversalReading
        EachMotionIsLocalToChangingSubject TimeIsEverywhereAlike)
    (hBridge :
      MotionTimeScopeDifferenceEntailsNonidentityReading
        EachMotionIsLocalToChangingSubject TimeIsEverywhereAlike TimeIsMotion) :
    TimeIsNotMotionReading TimeIsMotion := by
  exact hBridge hScope

end TruthCore.Results.Aristotle.Physics.TimeIsNotMotion
