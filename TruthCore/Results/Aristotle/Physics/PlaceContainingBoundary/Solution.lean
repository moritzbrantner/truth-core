import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter4

namespace TruthCore.Results.Aristotle.Physics.PlaceContainingBoundary

open TruthCore.Greek.Aristotle.Physics

/-- Eliminating form, matter, and independent interval leaves the containing boundary. -/
theorem placeIsContainingBoundary
    (PlaceIsForm PlaceIsMatter PlaceIsIndependentInterval
      PlaceIsContainingBoundaryAtContact : Prop)
    (hCandidates :
      FourPlaceCandidatesReading PlaceIsForm PlaceIsMatter PlaceIsIndependentInterval
        PlaceIsContainingBoundaryAtContact)
    (hExcluded :
      FormMatterIntervalExcludedReading PlaceIsForm PlaceIsMatter
        PlaceIsIndependentInterval) :
    PlaceIsContainingBoundaryAtContactReading PlaceIsContainingBoundaryAtContact := by
  rcases hCandidates with hForm | hMatter | hInterval | hBoundary
  · exact False.elim (hExcluded.1 hForm)
  · exact False.elim (hExcluded.2.1 hMatter)
  · exact False.elim (hExcluded.2.2 hInterval)
  · exact hBoundary

end TruthCore.Results.Aristotle.Physics.PlaceContainingBoundary
