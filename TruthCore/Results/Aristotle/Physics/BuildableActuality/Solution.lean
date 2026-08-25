import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Results.Aristotle.Physics.BuildableActuality

open TruthCore.Greek.Aristotle.Physics

/--
If the actuality of the buildable qua buildable is either building or the completed house,
and the completed house is excluded as that actuality, then the actuality is building.
-/
theorem buildableActualityIsBuilding
    (BuildingIsActuality : Prop)
    (HouseIsActuality : Prop)
    (hAlternatives :
      BuildableActualityAlternativeReading BuildingIsActuality HouseIsActuality)
    (hHouseExcluded :
      CompletedHouseNotBuildableActualityReading HouseIsActuality) :
    BuildableActualityIsBuildingReading BuildingIsActuality := by
  exact Or.resolve_right hAlternatives hHouseExcluded

end TruthCore.Results.Aristotle.Physics.BuildableActuality
