import TruthCore.Greek.Aristotle.Physics.BookII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.MostPreciseCause

open TruthCore.Greek.Aristotle.Physics

/-- The builder/building-art chain reaches the more precise cause. -/
theorem buildingArtMostPreciseCause
    (HumanBuilds BuilderStatusExplainsBuilding
      BuildingArtIsMorePreciseCause : Prop)
    (hBuilder :
      HumanBuildsQuaBuilderReading
        HumanBuilds BuilderStatusExplainsBuilding)
    (hArt :
      BuilderBuildsThroughBuildingArtReading
        BuilderStatusExplainsBuilding BuildingArtIsMorePreciseCause) :
    BuildingArtMostPreciseCauseReading
      HumanBuilds BuildingArtIsMorePreciseCause := by
  intro hBuilds
  exact hArt (hBuilder hBuilds)

end TruthCore.Results.Aristotle.Physics.MostPreciseCause
