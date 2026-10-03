import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter2

namespace TruthCore.Results.Aristotle.Physics.TimeMagnitudeContinuous

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's alternating-speed argument in *Physics* VI.2, 232b24-233a10. -/
theorem timeMagnitudeContinuous
    (TimeAlwaysFurtherDivisible MagnitudeAlwaysFurtherDivisible
      EveryTimeContinuous EveryMagnitudeContinuous : Prop)
    (hDivision :
      AlternatingSpeedsIndefinitelyDivideTimeMagnitudeReading
        TimeAlwaysFurtherDivisible MagnitudeAlwaysFurtherDivisible)
    (hTransition :
      AlwaysDivisibleTimeMagnitudeAreContinuousReading
        TimeAlwaysFurtherDivisible MagnitudeAlwaysFurtherDivisible
        EveryTimeContinuous EveryMagnitudeContinuous) :
    TimeAndMagnitudeContinuousReading EveryTimeContinuous EveryMagnitudeContinuous := by
  exact hTransition hDivision

end TruthCore.Results.Aristotle.Physics.TimeMagnitudeContinuous
