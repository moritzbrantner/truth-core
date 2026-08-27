import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter6

namespace TruthCore.Results.Aristotle.Physics.VoidFromMotionArgument

open TruthCore.Greek.Aristotle.Physics

/-- The reported motion argument concludes that void exists. -/
theorem voidFromMotion
    (LocalMotionAndIncreaseOccur VoidExists : Prop)
    (hMotion : LocalMotionAndIncreaseOccurReading LocalMotionAndIncreaseOccur)
    (hBridge : MotionArgumentRequiresVoidReading LocalMotionAndIncreaseOccur VoidExists) :
    VoidExistsReading VoidExists := by
  exact hBridge hMotion

end TruthCore.Results.Aristotle.Physics.VoidFromMotionArgument
