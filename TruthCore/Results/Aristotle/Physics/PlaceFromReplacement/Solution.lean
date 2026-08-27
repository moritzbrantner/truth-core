import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter1

namespace TruthCore.Results.Aristotle.Physics.PlaceFromReplacement

open TruthCore.Greek.Aristotle.Physics

/-- Mutual bodily replacement establishes a place distinct from its occupants. -/
theorem placeDistinctFromOccupyingBodies
    (WaterAndAirOccupySameRegionAtDifferentTimes BodiesEnterAndLeaveRegion
      PlaceDistinctFromOccupyingBodies : Prop)
    (hReplacement :
      BodiesMutuallyReplaceInSameRegionReading
        WaterAndAirOccupySameRegionAtDifferentTimes BodiesEnterAndLeaveRegion)
    (hBridge :
      MutualReplacementImpliesDistinctPlaceReading
        WaterAndAirOccupySameRegionAtDifferentTimes BodiesEnterAndLeaveRegion
        PlaceDistinctFromOccupyingBodies) :
    PlaceDistinctFromOccupyingBodiesReading PlaceDistinctFromOccupyingBodies := by
  exact hBridge hReplacement

end TruthCore.Results.Aristotle.Physics.PlaceFromReplacement
