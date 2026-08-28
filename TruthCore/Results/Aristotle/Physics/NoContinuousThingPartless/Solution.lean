import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter2

namespace TruthCore.Results.Aristotle.Physics.NoContinuousThingPartless

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's speed-ratio reductio in *Physics* VI.2, 233b15-32. -/
theorem noContinuousThingPartless
    (FasterSlowerRatioConstruction DividesSupposedIndivisiblePart
      NoContinuousThingPartless : Prop)
    (hRatio :
      SpeedRatioDividesSupposedIndivisibleReading
        FasterSlowerRatioConstruction DividesSupposedIndivisiblePart)
    (hTransition :
      SpeedRatioDivisionImpliesNoContinuousPartlessReading
        FasterSlowerRatioConstruction DividesSupposedIndivisiblePart
        NoContinuousThingPartless) :
    NoContinuousThingPartlessReading NoContinuousThingPartless := by
  exact hTransition hRatio

end TruthCore.Results.Aristotle.Physics.NoContinuousThingPartless
