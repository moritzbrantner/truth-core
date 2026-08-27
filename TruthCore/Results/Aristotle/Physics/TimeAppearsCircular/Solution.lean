import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter14

namespace TruthCore.Results.Aristotle.Physics.TimeAppearsCircular

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's qualified circular-time argument in *Physics* IV.14, 223b23-224a2. -/
theorem timeAppearsCircular
    (TimeMeasuredByCircularMotion TimeAppearsCircular : Prop)
    (hMeasured : CircularMotionMeasuresTimeReading TimeMeasuredByCircularMotion)
    (hAppearance :
      CircularMeasurementMakesTimeAppearCircularReading
        TimeMeasuredByCircularMotion TimeAppearsCircular) :
    TimeAppearsCircularReading TimeAppearsCircular := by
  exact hAppearance hMeasured

end TruthCore.Results.Aristotle.Physics.TimeAppearsCircular
