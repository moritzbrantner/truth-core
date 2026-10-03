import TruthCore.Greek.Aristotle.Physics.BookII.Chapter1

namespace TruthCore.Results.Aristotle.Physics.AntiphonMaterialNature

open TruthCore.Greek.Aristotle.Physics

/-- Antiphon's sprouting-bed evidence conditionally supports the attributed material view. -/
theorem antiphonMaterialNature
    (BedMaterialSprouts WoodEmerges BedEmerges
      MaterialIsNature ArtificialArrangementIsNature : Prop)
    (hEvidence :
      AntiphonBedSproutingEvidenceReading
        BedMaterialSprouts WoodEmerges BedEmerges)
    (hSupports :
      AntiphonSproutingSupportsMaterialNatureReading
        WoodEmerges BedEmerges MaterialIsNature ArtificialArrangementIsNature) :
    AntiphonMaterialNatureConclusionReading
      BedMaterialSprouts MaterialIsNature ArtificialArrangementIsNature := by
  sorry

end TruthCore.Results.Aristotle.Physics.AntiphonMaterialNature
