import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10
namespace TruthCore.Results.Aristotle.Physics.PointDistanceNoIndivisibleMotion
open TruthCore.Greek.Aristotle.Physics
theorem pointDistanceNoIndivisibleMotion
    (PointMoves FirstTraversalEqualOrLess FirstTraversalEqual
      LineComposedOfPoints : Prop)
    (hFirst : MoverMustFirstTraverseEqualOrLessReading
      PointMoves FirstTraversalEqualOrLess)
    (hEqual : IndivisibleFirstTraversalMustEqualItselfReading
      FirstTraversalEqualOrLess FirstTraversalEqual)
    (hCompose : RepeatedPointTraversalsWouldComposeLineReading
      PointMoves FirstTraversalEqual LineComposedOfPoints)
    (hNoComposition : ContinuumNotComposedOfIndivisiblesReading
      LineComposedOfPoints) :
    NoIndivisibleCanMovePerSeReading PointMoves := by
  intro hMoves
  have hFirstTraversal := hFirst hMoves
  have hEqualTraversal := hEqual hFirstTraversal
  exact hNoComposition (hCompose ⟨hMoves, hEqualTraversal⟩)
end TruthCore.Results.Aristotle.Physics.PointDistanceNoIndivisibleMotion
