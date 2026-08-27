import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter8

namespace TruthCore.Results.Aristotle.Physics.NoMotionInSeparatedVoid

open TruthCore.Greek.Aristotle.Physics

/-- Directionless void eliminates natural motion and therefore all motion. -/
theorem noMotionInSeparatedVoid
    (InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation
      NaturalMotionInVoid AnyMotionInVoid : Prop)
    (hVoid :
      VoidLacksNaturalMotionReading InfiniteVoidHasUpDownOrMiddle
        VoidHasDirectionalDifferentiation NaturalMotionInVoid)
    (hNoDirections :
      VoidHasNoDirectionalDifferentiationReading
        InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation)
    (hDependence :
      NoNaturalMotionEntailsNoMotionReading NaturalMotionInVoid AnyMotionInVoid) :
    NoMotionInSeparatedVoidReading AnyMotionInVoid := by
  exact hDependence (hVoid hNoDirections)

end TruthCore.Results.Aristotle.Physics.NoMotionInSeparatedVoid
