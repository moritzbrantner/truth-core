import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter12

namespace TruthCore.Results.Aristotle.Physics.TimeMotionMutualMeasurement

open TruthCore.Greek.Aristotle.Physics

/-- The two source-stated measurement directions establish reciprocal measurement. -/
theorem timeMotionMutualMeasurement
    (TimeMeasuresMotion MotionMeasuresTime : Prop)
    (hTime : TimeMeasuresMotionReading TimeMeasuresMotion)
    (hMotion : MotionMeasuresTimeReading MotionMeasuresTime) :
    TimeAndMotionMeasureOneAnotherReading TimeMeasuresMotion MotionMeasuresTime := by
  sorry

end TruthCore.Results.Aristotle.Physics.TimeMotionMutualMeasurement
