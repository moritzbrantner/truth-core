import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter9
namespace TruthCore.Results.Aristotle.Physics.RotatingBodiesNeverRest
open TruthCore.Greek.Aristotle.Physics
theorem rotatingBodiesNeverRest
    (RotatingBodyRests WholeAndPartsSameThroughTime : Prop)
    (hRestCriterion : RestRequiresWholeAndPartsSameThroughTimeReading
      RotatingBodyRests WholeAndPartsSameThroughTime)
    (hPartsMove : RotatingPartsNeverStableInPlaceReading
      WholeAndPartsSameThroughTime) :
    RotatingBodiesNeverRestReading RotatingBodyRests := by
  sorry
end TruthCore.Results.Aristotle.Physics.RotatingBodiesNeverRest
