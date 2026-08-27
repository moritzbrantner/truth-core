import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter2

namespace TruthCore.Results.Aristotle.Physics.PlaceNeitherFormNorMatter

open TruthCore.Greek.Aristotle.Physics

/-- Separability and containment exclude place from being either form or matter. -/
theorem placeNeitherFormNorMatter
    (BodiesReplaceOneAnother VesselIsMovablePlace PlaceSeparableFromOccupant
      PlaceContainsOccupant PlaceIsPartOfOccupant PlaceIsStateOfOccupant
      PlaceIsForm PlaceIsMatter : Prop)
    (hPlace :
      PlaceSeparableContainerReading
        BodiesReplaceOneAnother VesselIsMovablePlace PlaceSeparableFromOccupant
        PlaceContainsOccupant PlaceIsPartOfOccupant PlaceIsStateOfOccupant)
    (hBridge :
      SeparabilityAndContainmentExcludeFormMatterReading
        PlaceSeparableFromOccupant PlaceContainsOccupant PlaceIsForm PlaceIsMatter) :
    PlaceNeitherFormNorMatterReading PlaceIsForm PlaceIsMatter := by
  sorry

end TruthCore.Results.Aristotle.Physics.PlaceNeitherFormNorMatter
