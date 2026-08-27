import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter11

namespace TruthCore.Results.Aristotle.Physics.TimeBelongsToMotion

open TruthCore.Greek.Aristotle.Physics

/-- Time is not motion but cannot exist without it, so it belongs to motion. -/
theorem timeBelongsToMotion
    (TimeIsMotion TimeExistsWithoutMotion TimeBelongsToMotion : Prop)
    (hNotMotion : TimeIsNotMotionReading TimeIsMotion)
    (hDependence : TimeCannotExistWithoutMotionReading TimeExistsWithoutMotion)
    (hBridge :
      TimeNonidentityAndDependenceEntailBelongingToMotionReading
        TimeIsMotion TimeExistsWithoutMotion TimeBelongsToMotion) :
    TimeBelongsToMotionReading TimeBelongsToMotion := by
  exact hBridge ⟨hNotMotion, hDependence⟩

end TruthCore.Results.Aristotle.Physics.TimeBelongsToMotion
