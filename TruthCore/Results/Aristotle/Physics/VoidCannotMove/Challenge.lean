import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter9

namespace TruthCore.Results.Aristotle.Physics.VoidCannotMove

open TruthCore.Greek.Aristotle.Physics

/-- Void cannot move because motion would require an impossible place for void. -/
theorem voidCannotMove
    (VoidMoves PlaceForVoidExists : Prop)
    (hPlace : VoidMotionEntailsPlaceForVoidReading VoidMoves PlaceForVoidExists)
    (hNoPlace : PlaceForMovingVoidImpossibleReading PlaceForVoidExists) :
    VoidCannotMoveReading VoidMoves := by
  sorry

end TruthCore.Results.Aristotle.Physics.VoidCannotMove
