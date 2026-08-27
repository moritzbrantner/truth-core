import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter12

namespace TruthCore.Results.Aristotle.Physics.ThingsNeitherMovingNorRestingNotInTime

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's *Physics* IV.12 motion-rest scope argument, 221a7-10 and 221b18-27. -/
theorem thingsNeitherMovingNorRestingNotInTime
    (ThingIsInTime ThingBeingMeasuredByTime ThingMoves ThingRests : Prop)
    (hMeasured :
      BeingInTimeEntailsBeingMeasuredByTimeReading ThingIsInTime ThingBeingMeasuredByTime)
    (hScope :
      TemporalMeasurementEntailsMovingOrRestingReading
        ThingBeingMeasuredByTime ThingMoves ThingRests) :
    NeitherMovingNorRestingNotInTimeReading ThingMoves ThingRests ThingIsInTime := by
  sorry

end TruthCore.Results.Aristotle.Physics.ThingsNeitherMovingNorRestingNotInTime
