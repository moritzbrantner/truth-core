import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter1

namespace TruthCore.Results.Aristotle.Physics.PlaceNotBody

open TruthCore.Greek.Aristotle.Physics

/-- The dimensional puzzle excludes place from being a body. -/
theorem placeIsNotBody
    (PlaceHasThreeDimensions PlaceIsNotBody : Prop)
    (hDimensions : PlaceHasThreeDimensionsReading PlaceHasThreeDimensions)
    (hBridge :
      BodilyPlaceWouldDuplicateBodiesReading
        PlaceHasThreeDimensions PlaceIsNotBody) :
    PlaceIsNotBodyReading PlaceIsNotBody := by
  sorry

end TruthCore.Results.Aristotle.Physics.PlaceNotBody
