import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter9
namespace TruthCore.Results.Aristotle.Physics.ZenoArrowStationary
open TruthCore.Greek.Aristotle.Physics
theorem zenoArrowStationary (ArrowAtRestInEveryNow ArrowIsStationary : Prop)
    (hRest : ZenoArrowAtRestInEveryNowReading ArrowAtRestInEveryNow)
    (hEntails : RestInEveryNowEntailsStationaryArrowReading
      ArrowAtRestInEveryNow ArrowIsStationary) :
    ZenoArrowStationaryConclusionReading ArrowIsStationary := by
  sorry
end TruthCore.Results.Aristotle.Physics.ZenoArrowStationary
