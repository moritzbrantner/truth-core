import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter1
namespace TruthCore.Results.Aristotle.Physics.EveryMovingThingMoved
open TruthCore.Greek.Aristotle.Physics
theorem everyMovingThingMoved
    (MovingSubjectDivisible PartRestDeterminesWholeRest
      EveryMovingThingMovedBySomething : Prop)
    (hDivisible : EveryChangingSubjectDivisibleReading MovingSubjectDivisible)
    (hPart : DivisiblePrimaryMoverHasRestDeterminingPartReading
      MovingSubjectDivisible PartRestDeterminesWholeRest)
    (hDependence : RestDependenceEntailsMovedBySomethingReading
      PartRestDeterminesWholeRest EveryMovingThingMovedBySomething) :
    EveryMovingThingMovedBySomethingReading
      EveryMovingThingMovedBySomething := by
  sorry
end TruthCore.Results.Aristotle.Physics.EveryMovingThingMoved
