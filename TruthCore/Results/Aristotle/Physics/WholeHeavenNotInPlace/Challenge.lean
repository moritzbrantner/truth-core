import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter5

namespace TruthCore.Results.Aristotle.Physics.WholeHeavenNotInPlace

open TruthCore.Greek.Aristotle.Physics

/-- Without an external containing body, the whole heaven is not in place. -/
theorem wholeHeavenNotInPlace
    (ExternalBodyContainsWholeHeaven WholeHeavenIsInPlace
      NothingOutsideWholeHeaven : Prop)
    (hCondition :
      ExternalContainingBodyConditionReading
        ExternalBodyContainsWholeHeaven WholeHeavenIsInPlace)
    (hCosmos :
      NothingContainsWholeHeavenReading
        NothingOutsideWholeHeaven ExternalBodyContainsWholeHeaven) :
    WholeHeavenNotInPlaceReading WholeHeavenIsInPlace := by
  sorry

end TruthCore.Results.Aristotle.Physics.WholeHeavenNotInPlace
