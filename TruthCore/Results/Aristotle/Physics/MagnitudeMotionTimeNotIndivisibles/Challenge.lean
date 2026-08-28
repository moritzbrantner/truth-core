import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter1

namespace TruthCore.Results.Aristotle.Physics.MagnitudeMotionTimeNotIndivisibles

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's coordinated conclusion in *Physics* VI.1, 231b18-232a22. -/
theorem magnitudeMotionTimeNotComposedOfIndivisibles
    (MagnitudeComposedOfIndivisibles MotionComposedOfIndivisibles
      TimeComposedOfIndivisibles : Prop)
    (hMagnitude :
      ContinuumNotComposedOfIndivisiblesReading MagnitudeComposedOfIndivisibles)
    (hShared :
      MagnitudeMotionTimeIndivisibilityInterdependenceReading
        MagnitudeComposedOfIndivisibles MotionComposedOfIndivisibles
        TimeComposedOfIndivisibles) :
    MagnitudeMotionTimeNotComposedOfIndivisiblesReading
      MagnitudeComposedOfIndivisibles MotionComposedOfIndivisibles
      TimeComposedOfIndivisibles := by
  sorry

end TruthCore.Results.Aristotle.Physics.MagnitudeMotionTimeNotIndivisibles
