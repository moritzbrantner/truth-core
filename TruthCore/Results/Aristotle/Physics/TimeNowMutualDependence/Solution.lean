import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter11

namespace TruthCore.Results.Aristotle.Physics.TimeNowMutualDependence

open TruthCore.Greek.Aristotle.Physics

/-- The two source-stated dependence directions jointly establish mutual dependence. -/
theorem timeNowMutualDependence
    (TimeExists NowExists : Prop)
    (hNoTime : NoTimeEntailsNoNowReading TimeExists NowExists)
    (hNoNow : NoNowEntailsNoTimeReading TimeExists NowExists) :
    TimeAndNowMutuallyDependentReading TimeExists NowExists := by
  exact ⟨hNoTime, hNoNow⟩

end TruthCore.Results.Aristotle.Physics.TimeNowMutualDependence
