import TruthCore.Greek.Aristotle.Physics.BookII.Chapter1

namespace TruthCore.Results.Aristotle.Physics.GrowthTargetFormNature

open TruthCore.Greek.Aristotle.Physics

/-- The target of growth is both form and nature in Aristotle's Physics II.1 argument. -/
theorem growthTargetIsFormAndNature
    (GrowthReachesForm GrowthReachesMaterialSource GrowthReachesNature : Prop)
    (hNature : GrowthAsPathIntoNatureReading GrowthReachesNature)
    (hForm :
      GrowingTerminatesInFormNotMaterialReading
        GrowthReachesForm GrowthReachesMaterialSource) :
    GrowthTargetIsFormAndNatureReading
      GrowthReachesForm GrowthReachesNature := by
  sorry

end TruthCore.Results.Aristotle.Physics.GrowthTargetFormNature
