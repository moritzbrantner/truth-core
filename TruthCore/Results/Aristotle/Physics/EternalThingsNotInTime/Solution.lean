import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter12

namespace TruthCore.Results.Aristotle.Physics.EternalThingsNotInTime

open TruthCore.Greek.Aristotle.Physics

/-- Eternal things qua eternal are not in time because time does not measure their being. -/
theorem eternalThingsNotInTime
    (ThingIsEternalQuaEternal ThingIsInTime ThingBeingMeasuredByTime ThingAffectedByTime : Prop)
    (hMeasured :
      BeingInTimeEntailsBeingMeasuredByTimeReading ThingIsInTime ThingBeingMeasuredByTime)
      (hEternal :
        EternalThingNotMeasuredOrAffectedByTimeReading
          ThingIsEternalQuaEternal ThingBeingMeasuredByTime ThingAffectedByTime) :
    EternalThingNotInTimeReading ThingIsEternalQuaEternal ThingIsInTime := by
  intro hAlways hInTime
  exact (hEternal hAlways).1 (hMeasured hInTime)

end TruthCore.Results.Aristotle.Physics.EternalThingsNotInTime
