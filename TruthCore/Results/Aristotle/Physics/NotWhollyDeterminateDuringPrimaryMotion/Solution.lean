import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter8
namespace TruthCore.Results.Aristotle.Physics.NotWhollyDeterminateDuringPrimaryMotion
open TruthCore.Greek.Aristotle.Physics
theorem notWhollyDeterminateDuringPrimaryMotion
    (MovesInPrimaryTime WhollyDeterminateThroughTime ThingIsAtRest : Prop)
    (hDeterminateRest : WhollyDeterminateThroughTimeEntailsRestReading
      WhollyDeterminateThroughTime ThingIsAtRest)
    (hMotionExcludesRest : PrimaryMotionExcludesRestDuringTimeReading
      MovesInPrimaryTime ThingIsAtRest) :
    MovingThingNotWhollyDeterminateDuringPrimaryTimeReading
      MovesInPrimaryTime WhollyDeterminateThroughTime := by
  intro hMoves hDeterminate
  exact hMotionExcludesRest hMoves (hDeterminateRest hDeterminate)
end TruthCore.Results.Aristotle.Physics.NotWhollyDeterminateDuringPrimaryMotion
