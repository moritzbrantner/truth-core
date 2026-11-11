import TruthCore.Causality.ActualOnlyEuclidean

namespace TruthCore.Results.Causality.ActualOnlyEuclidean
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.ActualOnlyEuclidean
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)

/-- Local axioms 5 and 4 at `w` give local axiom 5 at every successor of `w`:
both targets are successors of `w` by transitivity at `w`, so Euclidean access
at `w` relates them. -/
theorem euclideanOnSuccessors {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : EuclideanAt frame w) (hTransitive : TransitiveAt frame w) :
    EuclideanOnSuccessors frame w := by
  sorry

/-- The two surrogate controls, by case analysis. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ActualOnlyEuclidean
